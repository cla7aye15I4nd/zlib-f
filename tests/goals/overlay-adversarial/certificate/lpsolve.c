/* maximize c.x s.t. A x <= b, x >= 0 (b any sign; big-M artificials). stdin: m n, rows "a1..an b", c. */
#include <stdio.h>
#include <stdlib.h>
int main(void){ int m,n; if(scanf("%d %d",&m,&n)!=2) return 1;
 double **A=malloc(sizeof(double*)*m), *b=malloc(sizeof(double)*m);
 int na=0; for(int i=0;i<m;i++){ A[i]=malloc(sizeof(double)*n); for(int j=0;j<n;j++) scanf("%lf",&A[i][j]); scanf("%lf",&b[i]); b[i]+=1e-6*(1+(i*7919)%101); if(b[i]<0) na++; }
 int N=n+m+na, W=N+1; double *T=calloc((size_t)(m+1)*W,sizeof(double)); int *B=malloc(sizeof(int)*m); const double BIG=1e7;
 double *c=malloc(sizeof(double)*n); for(int j=0;j<n;j++) scanf("%lf",&c[j]);
 double *z=&T[m*W]; for(int j=0;j<n;j++) z[j]=-c[j];
 int ai=0; for(int i=0;i<m;i++){ double s=b[i]<0?-1:1; for(int j=0;j<n;j++) T[i*W+j]=s*A[i][j]; T[i*W+n+i]=s; T[i*W+W-1]=s*b[i];
   if(b[i]<0){ int col=n+m+ai++; T[i*W+col]=1; B[i]=col; z[col]=BIG; } else B[i]=n+i; }
 for(int i=0;i<m;i++) if(B[i]>=n+m){ for(int j=0;j<W;j++) z[j]-=BIG*T[i*W+j]; }
 for(long it=0; it<2000000; it++){ int p=-1; double mn=-1e-9;
   for(int j=0;j<N;j++) if(z[j]<mn){mn=z[j];p=j; if(it>20000) break;}
   if(p<0) break; int r=-1; double best=0;
   for(int i=0;i<m;i++){ double a=T[i*W+p]; if(a>1e-11){ double q=T[i*W+W-1]/a; if(r<0||q<best-1e-12||(q<best+1e-12&&B[i]<B[r])){best=q;r=i;} } }
   if(r<0){ printf("unbounded\n\n\n"); return 0; }
   double pv=T[r*W+p]; for(int j=0;j<W;j++) T[r*W+j]/=pv;
   for(int i=0;i<=m;i++) if(i!=r){ double f=T[i*W+p]; if(f!=0) for(int j=0;j<W;j++) T[i*W+j]-=f*T[r*W+j]; }
   B[r]=p; }
 for(int i=0;i<m;i++) if(B[i]>=n+m && T[i*W+W-1]>1e-7){ printf("infeasible\n\n\n"); return 0; }
 printf("%.6f\n",z[W-1]); double *x=calloc(n,sizeof(double)); for(int i=0;i<m;i++) if(B[i]<n) x[B[i]]=T[i*W+W-1];
 for(int j=0;j<n;j++) printf("%.6f ",x[j]); printf("\n"); for(int i=0;i<m;i++) printf("%.6f ",z[n+i]); printf("\n"); return 0; }
