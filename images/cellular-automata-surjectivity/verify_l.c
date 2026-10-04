/* 独立検算: L 形 N={(0,0)a,(1,0)b,(2,0)c,(3,0)d,(0,1)e} の 5 サイト 2 値規則
   1) 4 サイト 1 次元規則の全射性を「ダイヤモンド（前単射性の破れ）」で判定（Moore 側）
   2) 行ごとの十分条件: 切替列 e と目標列 y のどんな組でも行の逆像がある
      （部分集合構成で空集合に到達しない）
   3) 5 点すべてに依存し、凸包の頂点 a, d, e のどれでも置換的でないものを数える */
#include <stdio.h>
#include <stdint.h>
static int bit(uint32_t t,int i){return (t>>i)&1;}
/* g: 16 ビットの真理値表, 入力 p|q<<1|r<<2|u<<3 */
static int surj1d(uint16_t g){
  /* 状態 s=(p,q,r) 3 ビット, 辺 s->t=(q,r,u), ラベル g(p,q,r,u) */
  int reach[64]={0}; int stack[64],sp=0;
  for(int s1=0;s1<8;s1++)for(int u1=0;u1<2;u1++)for(int u2=0;u2<2;u2++){
    if(u1==u2) continue;               /* 対角 (s,s) から非対角へ分かれる 1 歩 */
    int l1=bit(g,s1|u1<<3), l2=bit(g,s1|u2<<3);
    if(l1!=l2) continue;
    int t1=(s1>>1)|(u1<<2), t2=(s1>>1)|(u2<<2);
    int id=t1*8+t2; if(!reach[id]){reach[id]=1;stack[sp++]=id;}
  }
  while(sp){
    int id=stack[--sp]; int s1=id/8,s2=id%8;
    for(int u1=0;u1<2;u1++)for(int u2=0;u2<2;u2++){
      int l1=bit(g,s1|u1<<3), l2=bit(g,s2|u2<<3);
      if(l1!=l2) continue;
      int t1=(s1>>1)|(u1<<2), t2=(s2>>1)|(u2<<2);
      if(t1==t2) return 0;             /* 対角に戻った = ダイヤモンド = 全射でない */
      int nid=t1*8+t2; if(!reach[nid]){reach[nid]=1;stack[sp++]=nid;}
    }
  }
  return 1;
}
/* f: 32 ビット, 入力 a|b<<1|c<<2|d<<3|e<<4 */
static int rowcrit(uint32_t f){
  uint8_t succ[2][2][8]; /* succ[e][y][s] = 遷移先の集合 */
  for(int e=0;e<2;e++)for(int y=0;y<2;y++)for(int s=0;s<8;s++){
    uint8_t m=0;
    for(int u=0;u<2;u++){ int in=s|u<<3|e<<4; if(bit(f,in)==y) m|=1u<<((s>>1)|(u<<2)); }
    succ[e][y][s]=m;
  }
  int seen[256]={0}; int q[256],h=0,t=0; q[t++]=255; seen[255]=1;
  while(h<t){
    int m=q[h++];
    for(int e=0;e<2;e++)for(int y=0;y<2;y++){
      int nm=0; for(int s=0;s<8;s++) if(m>>s&1) nm|=succ[e][y][s];
      if(nm==0) return 0;
      if(!seen[nm]){seen[nm]=1;q[t++]=nm;}
    }
  }
  return 1;
}
static int depends(uint32_t f,int v){ for(int i=0;i<32;i++) if(bit(f,i)!=bit(f,i^(1<<v))) return 1; return 0; }
static int permutive(uint32_t f,int v){ for(int i=0;i<32;i++) if(bit(f,i)==bit(f,i^(1<<v))) return 0; return 1; }
int main(int argc,char**argv){
  static uint16_t S[65536]; int ns=0;
  for(int g=0;g<65536;g++) if(surj1d((uint16_t)g)) S[ns++]=(uint16_t)g;
  printf("1D 4-site surjective rules: %d\n",ns);
  long total=0,nonev=0,onlyb=0,onlyc=0,bothbc=0;
  for(int i=0;i<ns;i++)for(int j=0;j<ns;j++){
    uint32_t f=(uint32_t)S[i]|((uint32_t)S[j]<<16);
    int all=1; for(int v=0;v<5;v++) if(!depends(f,v)) {all=0;break;}
    if(!all) continue;
    if(permutive(f,0)||permutive(f,3)||permutive(f,4)) continue; /* 頂点 a,d,e */
    if(!rowcrit(f)) continue;
    total++;
    int pb=permutive(f,1), pc=permutive(f,2);
    if(!pb&&!pc) nonev++; else if(pb&&!pc) onlyb++; else if(!pb&&pc) onlyc++; else bothbc++;
  }
  printf("row-criterion surjective, all 5 sites, not slice-permutive: %ld\n",total);
  printf("  permutive nowhere %ld, only b %ld, only c %ld, both b,c %ld\n",nonev,onlyb,onlyc,bothbc);
  /* 例 A: f = !b xor (e & !a & !c & d) */
  uint32_t A=0,B=0;
  for(int in=0;in<32;in++){
    int a=in&1,b=in>>1&1,c=in>>2&1,d=in>>3&1,e=in>>4&1;
    if((!b)^(e&&!a&&!c&&d)) A|=1u<<in;
    int s=a^e, v;
    if(!s) v = b ? !c : (c||d); else v = b ? (!c&&!d) : c;
    if(v) B|=1u<<in;
  }
  uint32_t ex[2]={A,B}; const char*nm[2]={"A","B"};
  for(int k=0;k<2;k++){
    uint32_t f=ex[k];
    printf("example %s: tt=0x%08x rowcrit=%d f0surj=%d f1surj=%d depends=",nm[k],f,rowcrit(f),surj1d(f&0xffff),surj1d(f>>16));
    for(int v=0;v<5;v++) printf("%d",depends(f,v));
    printf(" permutive=");
    for(int v=0;v<5;v++) printf("%d",permutive(f,v));
    printf("\n");
  }
  return 0;
}
