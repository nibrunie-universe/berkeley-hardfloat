#include "dut.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define ROUNDING_MODE io_roundingMode
#define DETECT_TININESS io_detectTininess

static void initialize_dut(dut& m)
{
}

static void parse_extF80_to_fn79(const char* hex, VlWide<3>& dst)
{
  char buf[21];
  size_t len = strlen(hex);
  memset(buf, '0', 20);
  buf[20] = '\0';
  if (len <= 20) memcpy(buf + (20 - len), hex, len);

  char hi_str[5];
  memcpy(hi_str, buf, 4);
  hi_str[4] = '\0';
  uint32_t sign_exp = (uint32_t)strtoul(hi_str, NULL, 16);
  uint64_t sig64 = strtoull(buf + 4, NULL, 16);
  uint64_t frac63 = sig64 & 0x7FFFFFFFFFFFFFFFULL;

  dst[0] = (uint32_t)(frac63 & 0xFFFFFFFFULL);
  dst[1] = (uint32_t)((frac63 >> 32) & 0x7FFFFFFFULL) | ((sign_exp & 1U) << 31);
  dst[2] = (sign_exp >> 1) & 0x7FFFU;
}

static int process_inputs(dut& m)
{
  char value[64];

  if (scanf("%s", value) != 1) {
    return 0;
  }
  parse_extF80_to_fn79(value, m.io_a);

  if (scanf("%s", value) != 1) {
    return 0;
  }
  parse_extF80_to_fn79(value, m.io_b);

  return 1;
}

static int process_outputs(dut& m)
{
  char value[64];

  // output
  if (scanf("%s", value) != 1) {
    return 0;
  }
  parse_extF80_to_fn79(value, m.io_expected_out);

  // exception flags
  if (scanf("%s", value) != 1) {
    return 0;
  }
  m.io_expected_exceptionFlags = strtoull(value, NULL, 16);

  return 1;
}
