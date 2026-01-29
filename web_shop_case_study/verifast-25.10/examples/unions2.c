#include <stdint.h>

typedef union
{
    int i;
    unsigned u;
} union_t;

int main ()
//@ requires true;
//@ ensures true;
{
  union_t x;
  
  x./*@activating@*/i = -42;
  //@ deactivate_union_member(x.i);
  
  x./*@activating@*/u = 42;
  //@ deactivate_union_member(x.u);
  
  return 0;
}


