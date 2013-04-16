#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <string.h>


#define MAX_ENTRIES 100 


//
//  command line option processing
//
int find_option( int argc, char **argv, const char *option )
{
    for( int i = 1; i < argc; i++ )
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

//
//  benchmarking program
//
int main( int argc, char **argv )
{
    int n[MAX_ENTRIES],c[MAX_ENTRIES],i,count=0,num,p[MAX_ENTRIES],nt16;
    double t[MAX_ENTRIES],slope[MAX_ENTRIES-1],ss[MAX_ENTRIES],sse[MAX_ENTRIES],grade,ssgrade,lssgrade,sse_avg,lsse_avg;

    if( find_option( argc, argv, "-h" ) >= 0 )
    {
        printf( "Options:\n" );
        printf( "-h to see this help \n" );
        printf( "-s <filename> to specify name of summary file \n");
        return 0;
    }
    
    char *savename = read_string( argc, argv, "-s", NULL );
    FILE *fread = savename ? fopen( savename, "r" ) : NULL;
     
   
    if(fread){
      fscanf (fread,"%d %d %lf",&n[count],&c[count],&t[count]);
      count++; p[0]=1;
      while( fscanf (fread,"%d %d %d %lf",&n[count],&c[count],&p[count],&t[count]) != EOF )
        count++;
    }
 
    num = count-1;
 
	ss[0] = sse[0] = t[0]/t[1];
    for (i=2; i<=num;i++) {
      ss[i-1] = t[0]/t[i];
	  sse[i-1] = ss[i-1]/p[i];
    }
 
    printf("\nStrong scaling estimates are :\n");
    for (i=0; i<num; i++){
      printf(" %7.2lf",ss[i]);
    }
    printf(" (speedup)\n");
    for (i=0; i<num; i++){
      printf(" %7.2lf",sse[i]);
    }
    printf(" (efficiency)    for\n");
    for (i=0; i<num; i++){
      printf(" %7d",p[i+1]);
    }
    printf(" threads/processors\n\n");

	sse_avg=0.0;
	for (i=0; i<num; i++){
          sse_avg+=sse[i];
	  if (p[i+1]==16)
	    break;
        }
	nt16=i+1;
	sse_avg/=nt16;
	  
	  printf("Average strong scaling efficiency (1-16): %7.2lf \n\n",sse_avg);
	  
	lsse_avg=0.0;
	for (; i<num; i++){
          lsse_avg+=sse[i];
        }
	lsse_avg/=num-nt16+1;
	
	  printf("Average strong scaling efficiency (16-256): %7.2lf \n\n",lsse_avg);

	  if (sse_avg > 0.8) ssgrade=100.00;
	  else if (sse_avg > 0.5) ssgrade=75.00 + 25.00 * (sse_avg-0.5)/0.3; 
	  else ssgrade = sse_avg/0.5 * 75.00;
	  
	  if (lsse_avg > 0.8) lssgrade=100.00;
	  else if (lsse_avg > 0.5) lssgrade=75.00 + 25.00 * (lsse_avg-0.5)/0.3; 
	  else lssgrade = lsse_avg/0.5 * 75.00;
	  
	  grade= 0.5 * ssgrade + 0.5 * lssgrade;
	  
	  printf("\nKnapsack UPC Grade = %7.2f\n\n",grade);

    fclose( fread );
    
    return 0;
}
