/* as far as I could determine, mutexes are 24 chars long on 32 bits,
   40 chars long on 64 bit linux machines // in fact the sizes vary greatly, just adjust them as you can */
/* typedef struct {char a[8]; void* b[4];} lock_t; */
/* typedef struct lock_t {char a[8]; void* b[4];} lock_t; //for mutex */
/* typedef struct lock_t {void* b[6];} lock_t; //for semaphore */
typedef struct lock_t {void* a[4];} lock_t; //for semaphore
typedef unsigned long int thread_t; // like pthread_t
typedef int cond_t;

void makelock(lock_t *lock);

void freelock(lock_t *lock);

void acquire(lock_t *lock);

void release(lock_t *lock);

void freelock2(lock_t *lock); //for recursive locks

void release2(lock_t *lock); //consumes the lock

void spawn(void* (*f)(void*), void* args);

void makecond(cond_t *cond);

void freecond(cond_t *cond);

void waitcond(cond_t *cond, lock_t *mutex);
//Pthreads only requires a mutex for wait

void signalcond(cond_t *cond);