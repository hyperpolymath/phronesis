# Configuration generation
{
  name = "my-app",
  replicas =
    let env = "dev" in
    if env == "prod" then 5
    else if env == "staging" then 3
    else 1,
  port = 8080,
  env = "dev",

  # Byte detection configuration (matches stdlib/ByteDetector.affine)
  byte_detection = {
    # C0 control character range (U+0000-U+001F, excluding TAB/LF/CR)
    c0_control = {
      min = 0x00,  # 0
      max = 0x1F,  # 31
      excluded = [0x09, 0x0A, 0x0D],  # TAB, LF, CR
    },

    # Known BOM byte sequences
    boms = {
      utf8 = [0xEF, 0xBB, 0xBF],
      utf16_be = [0xFE, 0xFF],
      utf16_le = [0xFF, 0xFE],
      utf32_be = [0x00, 0x00, 0xFE, 0xFF],
      utf32_le = [0xFF, 0xFE, 0x00, 0x00],
    },
  },
}
