#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

enum { VARIABLES = 5, VERTICES = 32, PERMUTATIONS = 120, INPUT_ACTIONS = 240 };
static uint8_t permutations[PERMUTATIONS][VARIABLES];
static int permutation_count = 0;
static uint32_t lookup[INPUT_ACTIONS][4][256];

static void generate_permutations_rec(int depth, uint8_t used, uint8_t *current) {
    if (depth == VARIABLES) {
        memcpy(permutations[permutation_count], current, VARIABLES);
        permutation_count += 1;
        return;
    }
    for (int value = 0; value < VARIABLES; ++value) {
        if ((used >> value) & 1U) continue;
        current[depth] = (uint8_t)value;
        generate_permutations_rec(depth + 1, (uint8_t)(used | (1U << value)), current);
    }
}

static void build_lookup(void) {
    uint8_t current[VARIABLES];
    generate_permutations_rec(0, 0, current);
    if (permutation_count != PERMUTATIONS) {
        fprintf(stderr, "internal permutation count failure\n");
        exit(2);
    }
    for (int p = 0; p < PERMUTATIONS; ++p) {
        for (int input_flip = 0; input_flip < 2; ++input_flip) {
            int action = 2 * p + input_flip;
            uint8_t source[VERTICES];
            for (int vertex = 0; vertex < VERTICES; ++vertex) {
                int mapped = 0;
                for (int coordinate = 0; coordinate < VARIABLES; ++coordinate) {
                    int bit = (vertex >> permutations[p][coordinate]) & 1;
                    bit ^= input_flip;
                    mapped |= bit << coordinate;
                }
                source[vertex] = (uint8_t)mapped;
            }
            for (int byte_index = 0; byte_index < 4; ++byte_index) {
                for (int byte_value = 0; byte_value < 256; ++byte_value) {
                    uint32_t transformed = 0;
                    for (int vertex = 0; vertex < VERTICES; ++vertex) {
                        int src = source[vertex];
                        if ((src >> 3) == byte_index &&
                            ((byte_value >> (src & 7)) & 1)) {
                            transformed |= UINT32_C(1) << vertex;
                        }
                    }
                    lookup[action][byte_index][byte_value] = transformed;
                }
            }
        }
    }
}

static inline uint32_t decode_u32le(const unsigned char *raw) {
    return ((uint32_t)raw[0]) | ((uint32_t)raw[1] << 8) |
           ((uint32_t)raw[2] << 16) | ((uint32_t)raw[3] << 24);
}

static inline uint32_t apply_action(uint32_t code, int action) {
    return lookup[action][0][code & 255U] |
           lookup[action][1][(code >> 8) & 255U] |
           lookup[action][2][(code >> 16) & 255U] |
           lookup[action][3][(code >> 24) & 255U];
}

static int usage(const char *program) {
    fprintf(stderr, "usage: %s CODES_U32LE EXPECTED_ROWS THREADS\n", program);
    return 2;
}

int main(int argc, char **argv) {
    if (argc != 4) return usage(argv[0]);
    char *end = NULL;
    uint64_t expected_rows = strtoull(argv[2], &end, 10);
    if (end == argv[2] || *end != '\0') return usage(argv[0]);
    int threads = (int)strtol(argv[3], &end, 10);
    if (end == argv[3] || *end != '\0' || threads < 1) return usage(argv[0]);

    FILE *handle = fopen(argv[1], "rb");
    if (handle == NULL) { perror("cannot open code file"); return 2; }
    if (fseek(handle, 0, SEEK_END) != 0) {
        perror("cannot seek code file"); fclose(handle); return 2;
    }
    long raw_size = ftell(handle);
    if (raw_size < 0 || fseek(handle, 0, SEEK_SET) != 0) {
        perror("cannot size code file"); fclose(handle); return 2;
    }
    if ((uint64_t)raw_size != expected_rows * UINT64_C(4)) {
        fprintf(stderr, "code file size disagrees with expected row count\n");
        fclose(handle); return 2;
    }
    unsigned char *raw = (unsigned char *)malloc((size_t)raw_size);
    if (raw == NULL) {
        fprintf(stderr, "cannot allocate code buffer\n"); fclose(handle); return 2;
    }
    if (fread(raw, 1, (size_t)raw_size, handle) != (size_t)raw_size) {
        fprintf(stderr, "cannot read complete code file\n");
        free(raw); fclose(handle); return 2;
    }
    fclose(handle);

    build_lookup();
    omp_set_num_threads(threads);
    uint64_t bad_count = 0;
    uint64_t first_bad_index = UINT64_MAX;
    uint32_t first_bad_code = 0;
    double started = omp_get_wtime();

    #pragma omp parallel for schedule(static) reduction(+:bad_count)
    for (uint64_t index = 0; index < expected_rows; ++index) {
        uint32_t code = decode_u32le(raw + 4 * index);
        uint32_t minimum = code;
        for (int action = 0; action < INPUT_ACTIONS; ++action) {
            uint32_t transformed = apply_action(code, action);
            uint32_t complemented = ~transformed;
            if (transformed < minimum) minimum = transformed;
            if (complemented < minimum) minimum = complemented;
            if (minimum < code) break;
        }
        if (minimum != code) {
            bad_count += 1;
            #pragma omp critical
            {
                if (index < first_bad_index) {
                    first_bad_index = index;
                    first_bad_code = code;
                }
            }
        }
    }
    double elapsed = omp_get_wtime() - started;
    free(raw);
    if (bad_count != 0) {
        printf("{\"ok\":false,\"rows\":%" PRIu64
               ",\"noncanonical\":%" PRIu64
               ",\"first_bad_index\":%" PRIu64
               ",\"first_bad_code\":%" PRIu32
               ",\"group_size\":480,\"seconds\":%.6f}\n",
               expected_rows, bad_count, first_bad_index, first_bad_code, elapsed);
        return 1;
    }
    printf("{\"ok\":true,\"rows\":%" PRIu64
           ",\"noncanonical\":0,\"group_size\":480,"
           "\"input_actions_checked_per_row\":240,\"seconds\":%.6f}\n",
           expected_rows, elapsed);
    return 0;
}
