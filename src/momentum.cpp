#include <boost/unordered_map.hpp>
#include <iostream>
#include <openssl/sha.h>
#include "momentum.h"
#include <boost/date_time/posix_time/posix_time.hpp>
#define DEBUG_TIMING 0

#if DEBUG_TIMING
using namespace boost::posix_time;
#endif

namespace bts 
{
        #define NONCE_BITS 26
	#define MAX_MOMENTUM_NONCE  (1<<NONCE_BITS)
	#define SEARCH_SPACE_BITS 50
	#define BIRTHDAYS_PER_HASH 8

        #define FILTER_SLOTS_POWER 19  /* 2^20 bits - fits in L2 */
        #define FILTER_SIZE_BYTES (1 << (FILTER_SLOTS_POWER+1-3))
        #define PARTITION_BITS     10 /* Balance TLB pressure vs filter */

        #define HASH_MASK ((1ULL<<(64-NONCE_BITS))-1)  /* How hash is stored in hashStore */

        #define MOMENTUM_COLHASH_SIZE 36 /* bytes */

  /*
   * Duplicate filter functions.  The duplicate filter is a saturating
   * unary counter with overflow detection:  On addition, the counter
   * for a particular item goes to 1.  Upon a second addition, it goes
   * to 11, and remains there thereafter.  is_in_filter_twice(item)
   * checks the high bit of the item's counter to determine if an item
   * was added more than once to the filter.
   */

void set_or_double(uint32_t *filter, uint32_t whichbit) {
  uint32_t whichword = whichbit/16;
  uint32_t old = filter[whichword];
  uint32_t bitpat = 1UL << (2*(whichbit%16));
  /* no conditional: set 2nd bit of pair if 1st already set, 1st otherwise */
  filter[whichword] = old | (bitpat + (old&bitpat));
}

inline
void add_to_filter(uint32_t *filter, const uint64_t hash) {
      uint32_t whichbit = (uint32_t(hash) & ((1UL<<FILTER_SLOTS_POWER)-1));
      set_or_double(filter, whichbit);
}

inline
bool is_in_filter_twice(const uint32_t *filter, const uint64_t hash) {
      uint32_t whichbit = (uint32_t(hash) & ((1UL<<FILTER_SLOTS_POWER)-1));
      uint32_t cbits = filter[whichbit/16];
      return (cbits & (2UL<<(((whichbit&0xf)<<1))));
}

uint32_t *allocate_filter() {
      uint32_t *filter = (uint32_t *)malloc(FILTER_SIZE_BYTES);
      if (!filter) {
            printf("Error allocating memory for miner\n");
            return NULL;
      }
      return filter;
}

void free_filter(uint32_t *filter) {
      free(filter);
}

void reset_filter(uint32_t *filter) {
      memset(filter, 0x00, FILTER_SIZE_BYTES);
}

  /* The search procedure operates by generating all 2^26 momentum hash
   * values and storing them in a big table partitioned by 10 bits of
   * the hash.  It then detects duplicates within each partition.
   * The partitions go into a large chunk of memory, with a carefully-sized
   * gap between partitions, calculated so that the probability of
   * overrunning a partition is incredibly small.
   */

uint32_t partition_offset(uint32_t partition_id) {
      uint32_t partition_real_size = 1<<(NONCE_BITS-PARTITION_BITS);
      /* Leave a 3.125% space buffer.  This is safe with enough 9s of
       * probability to not matter.  Running over just gives bogus results
       * that are ignored during revalidation.  There is a larger gap
       * left at the end to ensure safety. */

      uint32_t partition_safe_size = partition_real_size + (partition_real_size>>5);
      return partition_id*partition_safe_size;
}


  /* Once a hash is placed in its partition bucket, the 26 high-order bits are
   * replaced with its momentum nonce number.  Of those 26 bits, 14 were unused
   * (64 bits - 50 momentum bits).  10 of those 14 were used to determine the
   * partition identifier (2^10 partitions).  4 are lost, which increases the
   * number of false collisions that must be re-validated, but it's not large. */

inline void put_hash_in_bucket(uint64_t hash, uint64_t *hashStore, uint32_t *hashCounts, uint32_t nonce) {
      uint32_t bin = hash & ((1<<PARTITION_BITS)-1);
      uint64_t hashval = ((uint64_t(nonce) << (64-NONCE_BITS)) | (hash >> (NONCE_BITS - (64 - SEARCH_SPACE_BITS)))); /* High-order bits now nonce */
      hashStore[hashCounts[bin]] = hashval;
      hashCounts[bin]++;
}


#define VECWIDTH 16

void generate_hashes(char *hash_tmp, uint64_t *hashStore, uint32_t *hashCounts) {
      uint64_t shacache[BIRTHDAYS_PER_HASH*VECWIDTH];
      uint32_t* index = (uint32_t*)hash_tmp;
      for ( uint32_t n = 0; n < MAX_MOMENTUM_NONCE; n += (BIRTHDAYS_PER_HASH*VECWIDTH)) {
            for (uint32_t i = 0; i < VECWIDTH; i++) {
                  *index = (n+(i*BIRTHDAYS_PER_HASH));
                  SHA512((unsigned char*)hash_tmp, MOMENTUM_COLHASH_SIZE, (unsigned char*)(shacache+i*BIRTHDAYS_PER_HASH));
            }
            for (uint32_t i = 0; i < BIRTHDAYS_PER_HASH*VECWIDTH; i++) {
                  put_hash_in_bucket((shacache[i] >> (64 - SEARCH_SPACE_BITS)), hashStore, hashCounts, n+i);
            }
            if (n%1048576==0) {
                  boost::this_thread::interruption_point();
	    }
      }
} 


/* Find duplicated hash values within a single partition.
* Validates that they are actual momentum 50 bit duplicates,
* and, if so, adds them to the list of results */

void find_duplicates(uint64_t *hashStore, uint32_t count, std::vector< std::pair<uint32_t,uint32_t> > &results, uint32_t *filter, uint256 head) 
{

  /* Three passes through the counting filter using different bits of the hash is
   * sufficient to eliminate nearly all false duplicates. */
  for (int pass = 0; pass < 3; pass++) {
    uint32_t shiftby = 0;
    if (pass == 1) shiftby = 19;
    if (pass == 2) shiftby = 9;

    reset_filter(filter);
    for (uint32_t i = 0; i < count; i++) {
      add_to_filter(filter, hashStore[i] >> shiftby);
    }
    
    uint32_t valid_entries = 0;

    for (uint32_t i = 0; i < count; i++) {
      if (is_in_filter_twice(filter, hashStore[i] >> shiftby)) {
	hashStore[valid_entries] = hashStore[i];
	valid_entries++;
      }
    }
    count = valid_entries;
  }

  /* At this point, there are typically 0 - but sometimes 2, 4, or 6 - items
   * remaining in the hashStore for this partition.  Identify the duplicates
   * and pass them in for hash revalidation.  This is an n^2 search, but the
   * number of items is so small it doesn't matter. */
   for (uint32_t i = 0; i < count; i++) {
     if (hashStore[i] == 0) { continue; }
     for (uint32_t j = i+1; j < count; j++) {
        if ((hashStore[i] & HASH_MASK) == (hashStore[j] & HASH_MASK)) {
          uint32_t nonce1 = hashStore[i] >> (64 - NONCE_BITS);
          uint32_t nonce2 = hashStore[j] >> (64 - NONCE_BITS);
          if (momentum_verify(head, nonce1, nonce2)) {
              /* Collisions can be used in both directions */
              results.push_back( std::make_pair( nonce1, nonce2 ) );
              results.push_back( std::make_pair( nonce2, nonce1 ) );
          }
        }
     }
   }
}


	
	std::vector< std::pair<uint32_t,uint32_t> > momentum_search( uint256 midHash )
  {
#if DEBUG_TIMING
      ptime time_start = microsec_clock::universal_time();
#endif
      std::vector< std::pair<uint32_t,uint32_t> > results;
      uint32_t *filter;
      filter = allocate_filter();
      if (!filter) {
            printf("Could not allocate filter for mining\n");
            return results;
      }


      uint32_t hashStoreSize = MAX_MOMENTUM_NONCE * sizeof(uint64_t);
      /* inter-partition margin of 3% plus a little extra at the end for
       * paranoia.  Missing things is OK 1 in a billion times, but 
       * crashing isn't, so the extra 1/64th at the end pushes the
       * probability of overrun down into the infestisimally small range.
       */

      hashStoreSize += ((hashStoreSize >> 5) + (hashStoreSize >> 6));
      uint64_t *hashStore = (uint64_t *)malloc(hashStoreSize);
      if (!hashStore) {
            free_filter(filter);
            printf("Could not allocate hashStore for mining\n");
            return results;
      }

      char  hash_tmp[sizeof(midHash)+4];
      memcpy((char*)&hash_tmp[4], (char*)&midHash, sizeof(midHash) );
      static const int NUM_PARTITIONS = (1<<PARTITION_BITS);
      uint32_t hashCounts[NUM_PARTITIONS];

      for (int i = 0; i < NUM_PARTITIONS; i++) { 
            hashCounts[i] = partition_offset(i);
      }

      generate_hashes(hash_tmp, hashStore, hashCounts);

      for (uint32_t i = 0; i < NUM_PARTITIONS; i++) {
	    int binStart = partition_offset(i);
	    int binCount = hashCounts[i] - binStart;
	    find_duplicates(hashStore+binStart, binCount, results, filter, midHash);
      }

      //for( auto itr = results.begin(); itr != results.end(); ++itr )
      //{
      //   assert( momentum_verify( midHash, itr->first, itr->second ) );
     // }
      //somap.destroy();
      free_filter(filter);
      free(hashStore);
#if DEBUG_TIMING
      ptime time_end = microsec_clock::universal_time();
      std::cout << "momentum search " << (time_end - time_start) << " s" << std::endl;
#endif
      return results;
   }


	uint64_t getBirthdayHash(const uint256& midHash, uint32_t a)
  {
    uint32_t index = a - (a%8);
    char  hash_tmp[sizeof(midHash)+4];
  //  std::cerr<<"midHash size:" <<sizeof(midHash)<<"\n";
    memcpy(&hash_tmp[4], (char*)&midHash, sizeof(midHash) );
    memcpy(&hash_tmp[0], (char*)&index, sizeof(index) );

    uint64_t  result_hash[8];
//      for( uint32_t i = 0; i < sizeof(hash_tmp); ++i )
 //     {
  //       std::cerr<<" "<<uint16_t((((unsigned char*)hash_tmp)[i]));
   //   }
//      std::cerr<<"\n";
		SHA512((unsigned char*)hash_tmp, sizeof(hash_tmp), (unsigned char*)&result_hash);
//    std::cerr<<"result_hash "<<a<<"  "<<a%8<<"  --- ";
 //   for( uint32_t i = 0; i < 8; ++i ) std::cerr<<result_hash[i]<<" ";
  //  std::cerr<<"\n";

    uint64_t r = result_hash[a%BIRTHDAYS_PER_HASH]>>(64-SEARCH_SPACE_BITS);
  //  std::cerr<<"bdayresult: "<<r<<"\n";
    return r;
	}

	bool momentum_verify( uint256 head, uint32_t a, uint32_t b ){
 //   std::cerr<<"verify  "<<a<<"  and "<<b<<"  mid: "<<head.ToString()<<"\n";
 //   std::cerr<<"    "<<getBirthdayHash(head,a)<<"   "<<getBirthdayHash(head,b)<<"\n";
		if( a == b ) return false;
		if( a > MAX_MOMENTUM_NONCE ) return false;
		if( b > MAX_MOMENTUM_NONCE ) return false;		

     bool r = (getBirthdayHash(head,a) == getBirthdayHash(head,b));
  //   std::cerr<< "####### Verified "<<int(r)<<"\n";
     return r;
	}

}
