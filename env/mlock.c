#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/resource.h>


int main() {
  struct rlimit rlp;
  int ret;

  ret = getrlimit(RLIMIT_MEMLOCK, &rlp);
  if (ret != 0) {
    printf("getrlimit RLIMIT_MEMLOCK failed %s (%d)\n",
	   strerror(errno), errno);
    return 1;
  }

  printf("[mlock] soft limit: %llu, hard limit: %llu\n",
	 (unsigned long long)rlp.rlim_cur,
	 (unsigned long long)rlp.rlim_max);

  if (rlp.rlim_cur < rlp.rlim_max) {
    rlp.rlim_cur = rlp.rlim_max;

    ret = setrlimit(RLIMIT_MEMLOCK, &rlp);
    if (ret != 0) {
      printf("setrlimit RLIMIT_MEMLOCK failed %s (%d)\n",
	     strerror(errno), errno);
      return 1;
    }

    ret = getrlimit(RLIMIT_MEMLOCK, &rlp);
    if (ret != 0) {
      printf("getrlimit RLIMIT_MEMLOCK failed %s (%d)\n",
	     strerror(errno), errno);
      return 1;
    }

    printf("[mlock] soft limit: %llu, hard limit: %llu\n",
	   (unsigned long long)rlp.rlim_cur,
	   (unsigned long long)rlp.rlim_max);
  }

  return 0;
}
