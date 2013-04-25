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
#define BCOUNT 20
#define BLOCKING NRITEMS*BCOUNT
//
// auxiliary functions
//
inline int max( int a, int b ) { return a > b ? a : b; }
inline int min( int a, int b ) { return a < b ? a : b; }

shared [BLOCKING] int *table;
/* shared [BLOCKING] int *ready; */


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
    if( MYTHREAD == 0 ){
        printf("\n");
        for(i=0; i< nitems; i++){
            for(j=0; j < (cap+1); j++){
                    printf("%02d ", T[i+j*nitems]);
            }
            printf("\n");
        }
        printf("\n");
    }
}

void print_table_affinity(int nitems, int cap, shared [BLOCKING] int *T){
    size_t i, j;
    if( MYTHREAD == 0 ){
        printf("\n");
        for(i=0; i< nitems; i++){
            for(j=0; j < (cap+1); j++){
                printf("%02ul ",(unsigned int) upc_threadof(&T[i+j*nitems]));
            }
            printf("\n");
        }
        printf("\n");
    }
}


void print_table_s(int nitems, int cap, int *T){
    int i, j;
    printf("\n");
        for(i=0; i < (cap+1); i++){
            for(j=0; j< nitems; j++){
            printf("%02d ", T[j+i*nitems]);
        }
        printf("\n");
    }
    printf("\n");

}

//
//  solvers
//
int build_table( int nitems, int cap, shared [BLOCKING] int *T, shared int *w, shared int *v )
{
    int wi, vi;
    size_t column;
    size_t shift, end;
    size_t i, j;
    
    wi = w[0];
    vi = v[0];

    upc_forall( j = 0;  j <  wi;  j++; &T[j*nitems] ){
        T[j*nitems] = 0;
    }
    upc_forall( j = wi; j <= cap; j++; &T[j*nitems] ){
        T[j*nitems] = vi;
    }

    
    
    /* upc_barrier; */

    
    /*
     * memory is set up
     *
     *  |   0 | nitems   |
     *  |   1 | nitems+1 |
     *  |   2 | ...      |
     *  |   3 |          |
     *  |   4 |          |
     *  | ... |          |
     *
     * T[i,j] = T[i+j*nitems]
     *
     *
     * 
     */
    /* print_table_affinity(nitems, cap, origin); */
    int* local_T = (int *)&T;
    /* for(column = 0; column< /BCOUNT; column++){ */
    for(column = 0; column< (MAXCAPACITY/BCOUNT)+1; column++){
        shift = column*BCOUNT;
        end = min(shift+BCOUNT, MAXCAPACITY+1);
        if(MYTHREAD == upc_threadof(&T[shift*nitems])){
            local_T = (int *)&T[shift*nitems];
        }
        upc_forall(i=1; i<nitems; i++; &T[i+shift*nitems]){
            wi = w[i];
            vi = v[i];
            /* upc_forall(j=shift; j<end; j++; &T[i+j*nitems]){ */
            for(j=shift; j<end; j++){
                /* assert( upc_threadof(&T[i+j*nitems]) == MYTHREAD); */
                /* w_i > w */
                if(w[i] > j){
                    local_T[i+(j-shift)*nitems] = local_T[(i-1)+(j-shift)*nitems];
                }
                else{
                    while(T[(i-1)+(j-w[i])*nitems] < 0){ }
                    local_T[i+(j-shift)*nitems] = max(local_T[(i-1)+(j-shift)*nitems],T[(i-1)+(j-wi)*nitems]+vi);
                }
                
            }                
        }
        
    }

#if PRINT==1
    print_table(nitems, cap, origin);
    print_table_affinity(nitems, cap, origin);
#endif
    upc_barrier;
    if( MYTHREAD != 0 )
        return 0;
    return T[(cap+1)*nitems-1];
}

void backtrack( int nitems, int cap, shared [BLOCKING] int *T, shared int *w, shared int *u )
{
    if( MYTHREAD != 0 )
        return;
    int index;
    index = nitems*(cap+1) - 1;
    int item;
    for(item=nitems-1; item >0; item--){
        u[item] = T[index] != T[index-1];
        index -= 1 + nitems*(u[item] ? w[item] : 0 );
    }
    u[0] = T[index] != 0; 
    /* i = nitems*(cap+1) - 1; */
    /* for( j = nitems-1; j > 0; j-- ) */
    /* { */
    /*     u[j] = T[i] != T[i-cap-1]; */
    /*     i -= cap+1 + (u[j] ? w[j] : 0 ); */
    /* } */
    /* u[0] = T[i] != 0; */
}

//
//  serial solver to check correctness
//
int solve_serial( int nitems, int cap, shared int *w, shared int *v )
{
    int i, j, best, *allocated, *T, wj, vj;

    //alloc local resources
    T = allocated = malloc( nitems*(cap+1)*sizeof(int) );
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
    table =  (shared [BLOCKING] int *) upc_all_alloc((nitems*(capacity+1)), 1*sizeof(int));
    /* ready =  (shared [BLOCKING] int *) upc_all_alloc((nitems*(capacity+1)), 1*sizeof(int)); */
    if( !weight || !value || !used || !table )
    {
        fprintf( stderr, "Failed to allocate memory" );
        upc_global_exit( -1 );
    }

    upc_forall( i = 0;  i <  nitems*(capacity+1);  i++; &table[i] ){
        table[i] = -1;
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

    best_value = build_table( nitems, capacity, table, weight, value );

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
        upc_free( used );
    }

    return 0;
}
