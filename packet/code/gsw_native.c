/* Independent C implementation of spherical map checks and literal Definition 1(a).
 * No canonical encoding: identity of negatives is checked in Python separately.
 * ABI returns 0 absent, 1 present with witness, negative on invalid input.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define NMAX 255
static int has(const uint64_t bits[4],int v){return (bits[v>>6]>>(v&63))&1;}
int r002_check(int n,const uint8_t *degree,const uint8_t *edges,int *witness){
 int8_t pos[NMAX][NMAX];uint64_t bits[NMAX][4];
 uint8_t seen[NMAX][6],reach[NMAX];int queue[NMAX],pentagons=0,total=0,faces=0;
 if(witness)witness[0]=0;
 if(n<12||n>NMAX)return -1;
 memset(pos,-1,sizeof(pos));memset(bits,0,sizeof(bits));memset(seen,0,sizeof(seen));memset(reach,0,sizeof(reach));
 for(int u=0;u<n;u++){
  int d=degree[u];if(d!=5&&d!=6)return -2;pentagons+=d==5;total+=d;
  for(int i=0;i<d;i++){
   int v=edges[6*u+i];if(v>=n||v==u||pos[u][v]>=0)return -3;
   pos[u][v]=i;bits[u][v>>6]|=UINT64_C(1)<<(v&63);
  }
 }
 if(pentagons!=12)return -4;
 for(int u=0;u<n;u++)for(int i=0;i<degree[u];i++)if(pos[edges[6*u+i]][u]<0)return -5;
 int head=0,tail=1;queue[0]=0;reach[0]=1;
 while(head<tail){int u=queue[head++];for(int i=0;i<degree[u];i++){int v=edges[6*u+i];if(!reach[v]){reach[v]=1;queue[tail++]=v;}}}
 if(tail!=n)return -6;
 for(int u=0;u<n;u++)for(int i=0;i<degree[u];i++)if(!seen[u][i]){
  int x=u,j=i,length=0;
  do{
   if(seen[x][j]||++length>3)return -7;
   seen[x][j]=1;int y=edges[6*x+j],back=pos[y][x];x=y;j=(back+1)%degree[y];
  }while(x!=u||j!=i);
  if(length!=3)return -7;
  faces++;
 }
 if(n-total/2+faces!=2)return -8;
 /* Ensure that arbitrary adjacency triangles coincide with facial triangles. */
 for(int u=0;u<n;u++)for(int i=0;i<degree[u];i++){
  int v=edges[6*u+i],a=edges[6*u+(i+degree[u]-1)%degree[u]],b=edges[6*u+(i+1)%degree[u]],common=0;
  if(a==b||!has(bits[v],a)||!has(bits[v],b))return -9;
  for(int j=0;j<4;j++)common+=__builtin_popcountll(bits[u][j]&bits[v][j]);
  if(common!=2)return -9;
 }
 for(int p=0;p<n;p++)if(degree[p]==5)for(int j=0;j<5;j++){
  int q=edges[6*p+j];if(degree[q]!=6)continue;
  for(int side=0;side<2;side++){
   int path[NMAX],len=3;uint64_t used[4]={0,0,0,0};
   path[0]=p;path[1]=q;path[2]=edges[6*p+(j+(side?1:4))%5];
   for(int i=0;i<3;i++)used[path[i]>>6]|=UINT64_C(1)<<(path[i]&63);
   while(1){
    int a=path[len-3],b=path[len-2],c=path[len-1],idx=pos[b][c],d=degree[b];
    int x=edges[6*b+(idx+d-1)%d],y=edges[6*b+(idx+1)%d],next;
    if(a==x)next=y;else if(a==y)next=x;else return -10;
    if(has(used,next))break;
    if(len>=n)return -11;
    path[len++]=next;used[next>>6]|=UINT64_C(1)<<(next&63);
    if(len%2==0&&degree[next]==5&&degree[c]==6){
     if(witness){witness[0]=len;for(int i=0;i<len;i++)witness[i+1]=path[i];}return 1;
    }
   }
  }
 }
 return 0;
}
#ifndef R002_LIBRARY
int main(int argc,char **argv){
 int verdicts=argc>1&&!strcmp(argv[1],"--verdicts"),ipr=0;
 for(int i=1;i<argc;i++)if(!strcmp(argv[i],"--ipr"))ipr=1;
 struct timespec t0,t1;clock_gettime(CLOCK_MONOTONIC,&t0);
 unsigned long long count=0,negative=0;int n=fgetc(stdin);
 if(n=='>'){int prev=0,c;while((c=fgetc(stdin))!=EOF){if(prev=='<'&&c=='<')break;prev=c;}if(c==EOF)return 20;n=fgetc(stdin);}
 while(n!=EOF){
  if(n<12||n>NMAX)return 21;
  uint8_t d[NMAX]={0},a[NMAX*6]={0};int witness[NMAX+1];
  for(int u=0;u<n;u++){
   int v;while((v=fgetc(stdin))!=0){if(v==EOF||v>n||d[u]>=6)return 22;a[6*u+d[u]++]=(uint8_t)(v-1);}
  }
  int result=r002_check(n,d,a,witness);if(result<0){fprintf(stderr,"invalid graph %llu: %d\n",count+1,result);return 23;}
  if(ipr)for(int u=0;u<n;u++)if(d[u]==5)for(int i=0;i<5;i++)if(d[a[6*u+i]]==5)return 24;
  count++;negative+=result==0;
  if(verdicts)putchar(result?'1':'0');
  else if(!result){
   printf("{\"event\":\"negative\",\"carbon\":%d,\"adjacency\":[",2*n-4);
   for(int u=0;u<n;u++){if(u)putchar(',');putchar('[');for(int i=0;i<d[u];i++){if(i)putchar(',');printf("%d",a[6*u+i]);}putchar(']');}puts("]}");
  }
  n=fgetc(stdin);
 }
 clock_gettime(CLOCK_MONOTONIC,&t1);
 double seconds=t1.tv_sec-t0.tv_sec+(t1.tv_nsec-t0.tv_nsec)/1e9;
 FILE *f=verdicts?stderr:stdout;
 fprintf(f,"{\"event\":\"summary\",\"count\":%llu,\"literal_none\":%llu,\"seconds\":%.6f}\n",count,negative,seconds);
 if(ferror(stdin)||ferror(stdout)||fflush(stdout))return 25;
 return 0;
}
#endif
