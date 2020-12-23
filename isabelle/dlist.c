/* list nodes; no data field for now */
struct node {
  struct node *prev;
  struct node *next;
};

/* insert node 'nd' after node 'ptr' */
void insert_after(struct node* nd, struct node* ptr) {
  nd->prev = ptr;
  nd->next = ptr->next;
  
  if (ptr->next != 0) {
    ptr->next->prev = nd;
  }  
  ptr->next = nd;
}

/*
 * Determine if the given number 'n' is prime.
 * We return 0 if 'n' is composite, or non-zero if 'n' is prime.
 * Use the knowledge that even numbers are not prime except for 2
 */
unsigned int is_prime_2(unsigned int n)
{
  /* Numbers less than 2 are not prime. */
  if (n < 2) {
    return 0;
  }
  
  /* 2 is the only even number that is prime */
  if (n % 2 == 0) {
    return (n == 2);
  }
  
  /* Find the first non-trivial factor of 'n'. */
  unsigned int i = 3;
  while (n % i != 0) {
    i+=2;
  }

  /* If the first factor found is 'n', it is a prime */
  return (i == n);
}

/* dummy main function */
int main() {
  return 0;
}
