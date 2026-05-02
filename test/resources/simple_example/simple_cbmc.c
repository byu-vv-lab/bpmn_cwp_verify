#include <assert.h>

int main() {
    int x;

    __CPROVER_assume(x == 0); // initial state from state.txt
    // __CPROVER_assume(x == 10); // This causes the verifier to fail.
    // QUESTION: Is bad_state.txt is being used for the
    // parser to raise an error over the actual verifier?

    assert(x <= 5);

    while (x <= 5)
        x += 1;

    assert(x > 5);  // verify the loop terminates with x > 5
    return 0;
}
