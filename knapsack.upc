#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <upc_relaxed.h>
#include <math.h>

#define NRITEMS 50000
#define MAXCAPACITY 9999
#define PRINT 0
#define BLOCKING (MAXCAPACITY+1)/4
//
// auxiliary functions
//
inline int max( int a, int b ) { return a > b ? a : b; }
inline int min( int a, int b ) { return a < b ? a : b; }

shared [BLOCKING] int *table;
shared [BLOCKING] int *ready;


double read_timer( )
{
    static int initialized = 0;
    static struct timeval start;
    struct timeval end;
    if( !initialized )
    {
        gettimeofday( &start, NULL );
        initialized = 1;
    }
    gettimeofday( &end, NULL );
    return (end.tv_sec - start.tv_sec) + 1.0e-6 * (end.tv_usec - start.tv_usec);
}


//
//  command line option processing
//
int find_option( int argc, char **argv, const char *option )
{
    int i;
    for(i = 1; i < argc; i++ )
        if( strcmp( argv[i], option ) == 0 )
            return i;
    return -1;
}

int read_int( int argc, char **argv, const char *option, int default_value )
{
    int iplace = find_option( argc, argv, option );
    if( iplace >= 0 && iplace < argc-1 )
        return atoi( argv[iplace+1] );
    return default_value;
}

char *read_string( int argc, char **argv, const char *option, char *default_value )
{
    int iplace = find_option( argc, argv, option );
    if( iplace >= 0 && iplace < argc-1 )
        return argv[iplace+1];
    return default_value;
}

void print_table(int nitems, int cap, shared [BLOCKING] int *T){
    int i, j;
    if( MYTHREAD != 0 ){
        printf("\n");
        for(j=0; j< nitems; j++){
            for(i=0; i < (cap+1); i++){
                printf("%02d ", T[i+j*(cap+1)]);
            }
            printf("\n");
        }
        printf("\n");
    }
}

void print_table_affinity(int nitems, int cap, shared [BLOCKING] int *T){
    int i, j;
    if( MYTHREAD != 0 ){
        printf("\n");
        for(j=0; j< nitems; j++){
            for(i=0; i < (cap+1); i++){
                printf("%02d ", upc_threadof(&T[i+j*(cap+1)]));
            }
            printf("\n");
        }
        printf("\n");
    }
}


void print_table_s(int nitems, int cap, int *T){
    int i, j;
    printf("\n");
    for(j=0; j< nitems; j++){
        for(i=0; i < (cap+1); i++){
            printf("%02d ", T[i+j*(cap+1)]);
        }
        printf("\n");
    }
    printf("\n");

}
//
//  solvers
//
int build_table( int nitems, int cap, shared [BLOCKING] int *T, shared [BLOCKING] int *ready, shared int *w, shared int *v )
{
    int wj, vj;
    double mytimer;
    double mytimer1;
    double starttime;
    shared [BLOCKING] int *origin = T;
    starttime = read_timer();

    
    wj = w[0];
    vj = v[0];
	
    int i;
    upc_forall( i = 0;  i <  wj;  i++; &T[i] ){
        T[i] = 0;
        ready[i] = 1;
    }
    upc_forall( i = wj; i <= cap; i++; &T[i] ){
        T[i] = vj;
        ready[i] = 1;
    }
    mytimer = read_timer() - starttime;
    upc_barrier;
    mytimer1 = read_timer() - starttime;
    printf("I am %d and setup took: %g \n", MYTHREAD, mytimer);
    printf("I am %d and setup took +barrier: %g \n", MYTHREAD, mytimer1);
    
    mytimer = 0;
    mytimer1 = 0;
    int j;
    for(j = 1; j < nitems; j++ )
    {
        wj = w[j];
        vj = v[j];
        int i;
        starttime = read_timer();
        upc_forall( i = 0;  i <  wj;  i++; &T[i] ){
            /* while(ready[i] < 1){fprintf( stderr, "waiting\n" );} */
            while(ready[i] < 1){}
            T[i+cap+1] = T[i];
            ready[i+cap+1] = 1;
        }
        mytimer += read_timer() - starttime;
        starttime = read_timer();
        upc_forall( i = wj; i <= cap; i++; &T[i] ){
            while(ready[i] < 1){ }
            while(ready[i-wj] < 1){ }
            /* while(ready[i] < 1){ fprintf( stderr, "waiting\n" );} */
            /* while(ready[i-wj] < 1){ fprintf( stderr, "waiting\n" );} */
            T[i+cap+1] = max( T[i], T[i-wj]+vj );
            ready[i+cap+1] = 1;
        }
        mytimer1 += read_timer() - starttime;
        /* upc_barrier; */

        T += cap+1;
        ready += cap+1;
    }
    /* mytimer = read_timer() - mytimer; */
    printf("I am %d and build_table main loop 0 took: %g \n", MYTHREAD, mytimer);
    printf("I am %d and build_table main loop 1 took: %g \n", MYTHREAD, mytimer1);
#if PRINT==1
    print_table(nitems, cap, origin);
    print_table_affinity(nitems, cap, origin);
#endif
    upc_barrier;
    if( MYTHREAD != 0 )
        return 0;
    return T[cap];
}

void backtrack( int nitems, int cap, shared [BLOCKING] int *T, shared int *w, shared int *u )
{
    int i, j;

    if( MYTHREAD != 0 )
        return;

    i = nitems*(cap+1) - 1;
    for( j = nitems-1; j > 0; j-- )
    {
        u[j] = T[i] != T[i-cap-1];
        i -= cap+1 + (u[j] ? w[j] : 0 );
    }
    u[0] = T[i] != 0;
}

//
//  serial solver to check correctness
//
int solve_serial( int nitems, int cap, shared int *w, shared int *v )
{
    int i, j, best, *allocated, *T, wj, vj;

    int *origin;
    //alloc local resources
    T = allocated = malloc( nitems*(cap+1)*sizeof(int) );
    origin = T;
    if( !allocated )
    {
        fprintf( stderr, "Failed to allocate memory" );
        upc_global_exit( -1 );
    }

    //build_table locally
    wj = w[0];
    vj = v[0];
    for( i = 0;  i <  wj;  i++ ) T[i] = 0;
    for( i = wj; i <= cap; i++ ) T[i] = vj;
    for( j = 1; j < nitems; j++ )
    {
        wj = w[j];
        vj = v[j];
        for( i = 0;  i <  wj;  i++ ) T[i+cap+1] = T[i];
        for( i = wj; i <= cap; i++ ) T[i+cap+1] = max( T[i], T[i-wj]+vj );
        T += cap+1;
    }
    best = T[cap];

    //free resources
    free( allocated );

    return best;
}

//
//  benchmarking program
//
int main( int argc, char** argv )
{
    int i, best_value, best_value_serial, total_weight, nused, total_value;
    double seconds;
    double mytimer;
    shared int *weight;
    shared int *value;
    shared int *used;
    shared int *total;

	if( find_option( argc, argv, "-h" ) >= 0 )
    {
        printf( "Options:\n" );
        printf( "-h to see this help\n" );
        printf( "-c <int> to set the knapsack capacity\n" );
        printf( "-n <nitems> to specify the number of items\n" );
        printf( "-s <filename> to specify a summary file name\n" );
        return 0;
    }
	
    //these constants have little effect on runtime
    int max_value  = 1000;
    int max_weight = 1000;

    //reading in problem size
    int capacity   = read_int( argc, argv, "-c", 999 );
    int nitems     = read_int( argc, argv, "-n", 5000 );


    /* Added to use the fixed sizes */
    capacity = MAXCAPACITY;
    nitems = NRITEMS;




    srand48( (unsigned int)time(NULL) + MYTHREAD );

    //allocate distributed arrays, use cyclic distribution
    weight = (shared int *) upc_all_alloc( nitems, sizeof(int) );
    value  = (shared int *) upc_all_alloc( nitems, sizeof(int) );
    used   = (shared int *) upc_all_alloc( nitems, sizeof(int) );
    //allocate distributed arrays, use blocked distribution
    table =  (shared [BLOCKING] int *) upc_all_alloc(nitems*4, ((capacity+1)/4)*sizeof(int));
ready =  (shared [BLOCKING] int *) upc_all_alloc(nitems*4, ((capacity+1)/4)*sizeof(int));
    if( !weight || !value || !used || !table )
    {
        fprintf( stderr, "Failed to allocate memory" );
        upc_global_exit( -1 );
    }

    upc_forall( i = 0;  i <  nitems*(capacity+1);  i++; &ready[i] ){
        ready[i] = 0;
    }

    // init
    max_weight = min( max_weight, capacity );//don't generate items that don't fit into bag
    upc_forall( i = 0; i < nitems; i++; i )
    {
        weight[i] = 1 + (lrand48()%max_weight);
        value[i]  = 1 + (lrand48()%max_value);
    }
    /* value[0] = 2; */
    /* value[1] = 3; */
    /* value[2] = 3; */
    /* value[3] = 4; */
    /* value[4] = 4; */
    /* value[5] = 5; */
    /* value[6] = 7; */
    /* value[7] = 8; */
    /* value[8] = 8; */

    /* weight[0] = 3; */
    /* weight[1] = 5; */
    /* weight[2] = 7; */
    /* weight[3] = 4; */
    /* weight[4] = 3; */
    /* weight[5] = 9; */
    /* weight[6] = 2; */
    /* weight[7] = 11; */
    /* weight[8] = 5; */
    
    upc_barrier;

    // time the solution
    seconds = read_timer( );
    mytimer = read_timer();

    best_value = build_table( nitems, capacity, table, ready, weight, value );

    mytimer = read_timer( ) - seconds;
    if( MYTHREAD == 0 ){
        printf("build_table took: %g \n",mytimer);
    }
    backtrack( nitems, capacity, table, weight, used );

    seconds = read_timer( ) - seconds;
    mytimer = seconds - mytimer;
    if( MYTHREAD == 0 ){
        printf("backtrack took: %g \n",mytimer);
    }    
    // check the result
    if( MYTHREAD == 0 )
    {
        printf( "%d items, capacity: %d, time: %g\n", nitems, capacity, seconds );
        mytimer = read_timer();

        best_value_serial = solve_serial( nitems, capacity, weight, value );
        mytimer = read_timer() - mytimer;
        printf( "%d items, capacity: %d, time: %g, serial_time: %g\n", nitems, capacity, seconds, mytimer );

        total_weight = nused = total_value = 0;
        for( i = 0; i < nitems; i++ )
            if( used[i] )
            {
                nused++;
                total_weight += weight[i];
                total_value += value[i];
            }

        printf( "%d items used, value %d, weight %d\n", nused, total_value, total_weight );

        if( best_value != best_value_serial || best_value != total_value || total_weight > capacity )
            printf( "WRONG SOLUTION\n" );

                // Doing summary data
                char *sumname = read_string( argc, argv, "-s", NULL );
                FILE *fsum = sumname ? fopen ( sumname, "a" ) : NULL;
                if( fsum)
                        fprintf(fsum,"%d %d %d %g\n",nitems,capacity,THREADS,seconds);
                if( fsum )
                        fclose( fsum );


        //release resources
        upc_free( weight );
        upc_free( value );
        upc_free( total );
        upc_free( used );
    }

    return 0;
}
