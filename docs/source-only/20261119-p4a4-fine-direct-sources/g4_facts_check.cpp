// Numeric replay of G4 Facts and coordinate-key uniqueness; not Lean/kernel.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
#include <vector>
using I=std::int64_t;
struct Plane { I base=0; std::array<I,6> c{}; };
struct Stats {std::uint64_t rows=0,negcorners=0,rowsneg=0,old_all=0,old_new=0; I min_gap=std::numeric_limits<I>::max(),max_gap=std::numeric_limits<I>::min(),min_ds=std::numeric_limits<I>::max(); std::array<std::uint64_t,6> third{},fifth{};};
Plane sub(Plane p,const Plane& q){p.base-=q.base;for(unsigned j=0;j<6;++j)p.c[j]-=q.c[j];return p;}
Plane coord(unsigned j,I k=256){Plane p;p.c[j]=k;return p;}
Plane total(){Plane p;p.c.fill(256);return p;}
Plane constant(I v){Plane p;p.base=v;return p;}
Plane rescue(){Plane p=constant(61200);p.c[2]=-96;return p;}
Plane tent(unsigned mask,bool descending){Plane p=constant(descending?91200:51200);for(unsigned j=0;j<6;++j)if(mask&(1u<<j))p.c[j]=descending?-384:128;return p;}
I lower(const Plane& p,const std::array<I,6>& lo){I x=p.base;for(unsigned j=0;j<6;++j)x+=p.c[j]*(lo[j]+(p.c[j]<0));return x;}
I upper(const Plane& p,const std::array<I,6>& lo){I x=p.base;for(unsigned j=0;j<6;++j)x+=p.c[j]*(lo[j]+(p.c[j]>=0));return x;}
bool above(const Plane& a,const Plane& b,const std::array<I,6>& lo){return lower(sub(a,b),lo)>=64;}
bool below(const Plane& a,I bound,const std::array<I,6>& lo){return upper(a,lo)<=bound;}
I signed_le64(const unsigned char* b){std::uint64_t u=0;for(unsigned j=0;j<8;++j)u|=std::uint64_t(b[j])<<(8*j);if((u>>63)==0)return static_cast<I>(u);if(u==(std::uint64_t(1)<<63))return std::numeric_limits<I>::min();return -static_cast<I>((~u)+1);}

bool check(const std::array<I,11>& row,Stats& st){
 const I grid=row[0],mask_signed=row[7],ds=row[8],old_res=row[9],new_res=row[10];std::array<I,6> lo{};for(unsigned j=0;j<6;++j)lo[j]=row[j+1];
 if(grid!=400||lo[0]+1>78||mask_signed<32||mask_signed>=64||old_res<=0||new_res<=0)return false;
 for(unsigned j=0;j<6;++j){if(lo[j]<8)return false;}
 for(unsigned j=0;j<5;++j){if(lo[j+1]+1>lo[j])return false;}
 unsigned mask=static_cast<unsigned>(mask_signed);Plane A=tent(mask,false),D=tent(mask,true),S=total(),H3{},H5{};
 H3.c={256,256,768,0,0,0};H5.c={256,256,256,256,768,0};
 constexpr std::array<unsigned,6> tm={0,1,3,7,5,6};bool third=false,fifth=false;
 for(unsigned j=0;j<6;++j){Plane x=j==0?rescue():tent(tm[j],false),y=j==0?rescue():tent(tm[j],true);
  if(!third&&above(x,H3,lo)&&above(y,H3,lo)){third=true;++st.third[j];}
  if(!fifth&&above(x,H5,lo)&&above(y,H5,lo)){fifth=true;++st.fifth[j];}}
 if(!third||!fifth||!above(A,constant(51200),lo)||!above(D,constant(51200),lo))return false;
 for(unsigned j=0;j<6;++j){Plane full{},remain{};for(unsigned k=0;k<6;++k){if(k<j)full.c[k]+=256;if(mask&(1u<<k))remain.c[k]+=256;if(k<j&&!(mask&(1u<<k)))remain.c[k]+=256;}full.c[j]+=512;remain.c[j]+=512;
  if(!above(A,full,lo)||!above(D,full,lo))return false;
  if(!(mask&(1u<<j))&&(!above(A,remain,lo)||!above(D,remain,lo)))return false;}
 Plane cubeA=sub(sub(A,S),coord(5,768)),cubeD=sub(sub(D,S),coord(5,768));if(!below(cubeA,0,lo)&&!below(cubeD,0,lo))return false;
 // Pick the same one of A,D,constant at the cell midpoint (first-minimum rule).
 std::array<unsigned,32> branch{};std::array<Plane,32> old{};old[0]=rescue();
 for(unsigned m=1;m<32;++m){I sm=0;for(unsigned j=0;j<5;++j)if(m&(1u<<j))sm+=2*lo[j]+1;
  I a=102400+128*sm,d=182400-384*sm;branch[m]=(a<=d&&a<=122400)?0:((d<=122400)?1:2);
  old[m]=branch[m]==0?tent(m,false):(branch[m]==1?tent(m,true):constant(61200));}
 bool all_old=true;for(const auto& p:old)if(!below(sub(p,S),old_res,lo)){all_old=false;break;}
 bool old_alt=below(sub(A,S),old_res,lo)||below(sub(D,S),old_res,lo);if(!all_old&&!old_alt)return false;
 if(!below(sub(A,S),new_res,lo)&&!below(sub(D,S),new_res,lo))return false;
 if(all_old)++st.old_all;else ++st.old_new;
 I sum=0,mingap=std::numeric_limits<I>::max(),maxgap=std::numeric_limits<I>::min();unsigned negative=0;
 for(unsigned corner=0;corner<64;++corner){std::array<I,6> x{};for(unsigned j=0;j<6;++j)x[j]=lo[j]+((corner>>j)&1u);I sums[32]{};
  for(unsigned m=1;m<32;++m){unsigned bit=static_cast<unsigned>(__builtin_ctz(m));sums[m]=sums[m&(m-1)]+x[bit];}
  I oldv=61200-96*x[2];for(unsigned m=1;m<32;++m){I v=branch[m]==0?51200+128*sums[m]:(branch[m]==1?91200-384*sums[m]:61200);oldv=std::max(oldv,v);}
  I sn=sums[mask&31u]+((mask&32u)?x[5]:0);I newv=std::min(51200+128*sn,91200-384*sn);I gap=newv-oldv;
  sum+=gap;mingap=std::min(mingap,gap);maxgap=std::max(maxgap,gap);if(gap<0)++negative;}
 if(sum!=ds)return false;
 ++st.rows;st.negcorners+=negative;if(negative)++st.rowsneg;st.min_gap=std::min(st.min_gap,mingap);st.max_gap=std::max(st.max_gap,maxgap);st.min_ds=std::min(st.min_ds,ds);
 return true;
}
int main(int argc,char** argv){
 bool micro=argc==3&&std::string(argv[1])=="--row";
 if(argc!=2&&!micro){std::cerr<<"usage: g4_facts [--row] ORIGINAL_NPY_OR_ROW\n";return 2;}
 std::ifstream f(argv[micro?2:1],std::ios::binary|std::ios::ate);if(!f){std::cerr<<"open failed\n";return 3;}
 if(micro){
  if(f.tellg()!=88){return 4;}
  f.seekg(0);std::array<unsigned char,88> raw{};if(!f.read(reinterpret_cast<char*>(raw.data()),raw.size()))return 5;
  std::array<I,11> row{};for(unsigned j=0;j<11;++j)row[j]=signed_le64(raw.data()+8*j);Stats st;bool ok=check(row,st);std::cout<<"{\"pass\":"<<(ok?"true":"false")<<"}\n";return ok?0:1;
 }
 if(f.tellg()!=55625280){std::cerr<<"wrong length\n";return 4;}f.seekg(128);
 Stats st;std::vector<std::uint64_t> keys;keys.reserve(632104);std::array<unsigned char,88> raw{};
 for(std::size_t i=0;i<632104;++i){if(!f.read(reinterpret_cast<char*>(raw.data()),raw.size()))return 5;std::array<I,11> row{};for(unsigned j=0;j<11;++j)row[j]=signed_le64(raw.data()+8*j);
  if(!check(row,st)){std::cerr<<"Facts failed row "<<i<<"\n";return 1;}
  std::uint64_t key=0;for(unsigned j=0;j<6;++j){if(row[j+1]>=128){std::cerr<<"key range\n";return 6;}key|=std::uint64_t(row[j+1])<<(7*j);}keys.push_back(key);
 }
 if(f.peek()!=std::char_traits<char>::eof())return 7;
 std::sort(keys.begin(),keys.end());if(std::adjacent_find(keys.begin(),keys.end())!=keys.end()){std::cerr<<"duplicate coordinate key\n";return 8;}
 std::cout<<"{\"pass\":true,\"rows\":"<<st.rows<<",\"keys_unique\":true,\"old_bound_all_old\":"<<st.old_all<<",\"old_bound_via_new\":"<<st.old_new
  <<",\"negative_corners\":"<<st.negcorners<<",\"rows_with_negative_corners\":"<<st.rowsneg<<",\"minimum_corner_gap_units\":"<<st.min_gap<<",\"maximum_corner_gap_units\":"<<st.max_gap<<",\"minimum_gap_sum_units\":"<<st.min_ds<<",\"third_first_witness\":[";
 for(unsigned j=0;j<6;++j){if(j)std::cout<<",";std::cout<<st.third[j];}std::cout<<"],\"fifth_first_witness\":[";for(unsigned j=0;j<6;++j){if(j)std::cout<<",";std::cout<<st.fifth[j];}std::cout<<"]}\n";
 return st.rows==632104?0:9;
}
