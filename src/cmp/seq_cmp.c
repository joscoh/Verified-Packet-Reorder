#include <stdint.h>

/* Compares two sequence numbers, dealing appropriate with wrapping.
 *
 * Parameters:
 * 	seq_a - the first sequence number to compare
 * 	seq_b - the second sequence number to compare
 *
 * Returns:
 * 	the result of subtracting seq_b from seq_a (seq_a - seq_b, in other
 * 	words), taking sequence number wraparound into account
 */
int seq_cmp (uint32_t seq_a, uint32_t seq_b)
{

        if (seq_a == seq_b) return 0;

        if (seq_a > seq_b)
                return (int)(seq_a - seq_b);
        else
                return (int)(UINT32_MAX - ((seq_b - seq_a) - 1));

}