/**
 * The smolnes NES emulator, crudely ported to Squirrel for Portal 2
 *
 * Some implementation notes: Squirrel doesn't have function closure
 * or really any similar system outside of static captures, so all
 * top-level variables are defined globally. Oh, and no types either.
 * Initial values are all 0, which (I think) matches C behavior.
 *
 * To simulate integer types, the toUint* functions are used wherever
 * a risk of an out-of-range value is conceivable. Logic may be altered
 * wherever post-increment decrement operators were used.
 *
 * Squirrel is a high-level language, with no support for pointer
 * magic, so the *rom and *chrrom pointers have been entirely removed,
 * and their logic has been inlined where applicable. *key_state also
 * had to go, but that makes more sense, given that we're not working
 * with hardware polling from SDL.
 *
 * There's also no "goto" equivalent in Squirrel (as is the case in
 * most sensible languages, really). To imitate that behavior, I check
 * the "goto" global on all lines below a jump. This is a megahack,
 * but it's the cleanest way to achieve this without changing the logic.
 *
 * On second thought, maybe smolnes was not the right project to fork
 * for this purpose, but oh well.
 *
 * I (p2r3) do NOT know how an NES emulator works at the low level.
 * Most of this is crude transliteration and guesswork.
 */

function toUint8 (x) { return x.tointeger() & 0xFF; }
function toUint16 (x) { return x.tointeger() & 0xFFFF; }
function toInt8 (x) {
  local u = x & 0xFF;
  return u >= 0x80 ? u - 0x100 : u;
}

// Whether to print debug information
::DBG <- 0;

::prg <- array(4, 0); ::chr <- array(8, 0);   // Current PRG/CHR banks
::prgbits <- 14; ::chrbits <- 12;       // Number of bits per PRG/CHR bank
::A <- 0; ::X <- 0; ::Y <- 0; ::P <- 4; ::S <- toUint8(~2); ::PCH <- 0; ::PCL <- 0; // CPU Registers
::addr_lo <- 0; ::addr_hi <- 0;                 // Current instruction address
::nomem <- 0;  // 1 => current instruction doesn't write to memory
::result <- 0; // Temp variabl)e
::val <- 0;    // Current instruction value
::cross <- 0;  // 1 => page crossing occurred
::tmp <- 0;    // Temp variables
::ppumask <- 0; ::ppuctrl <- 0; ::ppustatus <- 0; // PPU registers
::ppubuf <- 0;                      // PPU buffered reads
::W <- 0;                           // Write toggle PPU register
::fine_x <- 0;                      // X fine scroll offset, 0..7
::opcode <- 0;                      // Current instruction opcode
::nmi_irq <- 0;                     // 1 => IRQ occurred
                                       // 4 => NMI occurred
::ntb <- 0;                         // Nametable byte
::ptb_lo <- 0; ::ptb_hi <- 0;              // Pattern table low/high byte
::vram <- array(2048, 0);                  // Nametable RAM
::palette_ram <- array(64, 0);             // Palette RAM
::ram <- array(8192, 0);                   // CPU RAM
::chrram <- array(8192, 0);                // CHR RAM (only used for some games)
::prgram <- array(8192, 0);                // PRG RAM (only used for some games)
::oam <- array(256, 0);                    // Object Attribute Memory (sprite RAM)
::mask <- [128, 64, 1, 2,     // Masks used in branch instructions
          1,   0,  0, 1, 4, 0, 0, 4, 0,
          0,   64, 0, 8, 0, 0, 8]; // Masks used in SE*/CL* instructions.
::keys <- 0;                              // Joypad shift register
::mirror <- 0;                            // Current mirroring mode
::mmc1_bits <- 0; ::mmc1_data <- 0; ::mmc1_ctrl <- 0;   // Mapper 1 (MMC1) registers
::mmc3_chrprg <- array(8, 0); ::mmc3_bits <- array(8, 0);         // Mapper 4 (MMC3) registers
::mmc3_irq <- 0; ::mmc3_latch <- 0;              //
::chrbank0 <- 0; ::chrbank1 <- 0; ::prgbank <- 0;       // Current PRG/CHR bank
::rombuf <- array(1024 * 1024, 0);               // Buffer to read ROM file into

::key_state <- [
  0, // A
  0, // B
  0, // Select
  0, // Start
  0, // Dpad Up
  0, // Dpad Down
  0, // Dpad Left
  0, // Dpad Right
];

// uint16_t
::scany <- 0;                      // Scanline Y
::T <- 0; ::V <- 0;                // "Loopy" PPU registers
::sum <- 0;                        // Sum used for ADC/SBC
::dot <- 0;                        // Horizontal position of PPU, from 0..340
::atb <- 0;                        // Attribute byte
::shift_hi <- 0; ::shift_lo <- 0;  // Pattern table shift registers
::cycles <- 0;                     // Cycle count for current instruction
::frame_buffer <- array(61440, 0);    // 256x240 pixel frame buffer. Top and bottom 8 rows
                                   // are not drawn.
::goto <- null;

::shift_at <- 0;

// Read a byte from CHR ROM or CHR RAM.
function get_chr_byte(a) {
  a = toUint16(a);
  if (rombuf[5]) {
    return toUint8(rombuf[(16 + ((prg[1] + 1) << 14)) + (chr[a >>> chrbits] << chrbits | a & (1 << chrbits) - 1)]);
  } else {
    return toUint8(chrram[(chr[a >>> chrbits] << chrbits | a & (1 << chrbits) - 1)]);
  }
}

// Get the buffer address of a byte from CHR ROM or CHR RAM
// The caller is responsible for determining the applicable buffer
function get_chr_byte_idx(a) {
  a = toUint16(a);
  if (rombuf[5]) {
    return (16 + ((prg[1] + 1) << 14)) + (chr[a >>> chrbits] << chrbits | a & (1 << chrbits) - 1);
  } else {
    return (chr[a >>> chrbits] << chrbits | a & (1 << chrbits) - 1);
  }
}

// Get the buffer address of a byte from nametable RAM
function get_nametable_byte_idx(a) {
  a = toUint16(a);
  return        !mirror      ? a % 1024                  // single bank 0
               : mirror == 1 ? a % 1024 + 1024           // single bank 1
               : mirror == 2 ? a & 2047                  // vertical mirroring
                             : a / 2 & 1024 | a % 1024;  // horizontal mirroring
}

// Read a byte from nametable RAM.
function get_nametable_byte(a) {
  a = toUint16(a);
  return toUint8(vram[get_nametable_byte_idx(a)]);
}

// If `write` is non-zero, writes `val` to the address `hi:lo`, otherwise reads
// a value from the address `hi:lo`.
function mem(lo, hi, val, write) {
  lo = toUint8(lo); // 7
  hi = toUint8(hi); // 32
  val = toUint8(val); // 0
  write = toUint8(write); // 0

  local a = toUint16(hi << 8 | lo); // 8199

  // if (write) printl(lo + ":" + hi);

  switch (hi = toUint8(hi >>> 4)) { // hi = 2
  case 0: case 1: // $0000...$1fff RAM
    // printl("ram w=" + write + " a=" + a + " v=" + ram[a]);
    return toUint8(write ? ram[a] = val : ram[a]);

  case 2: case 3: // $2000..$2007 PPU (mirrored)
    lo = toUint8(lo & 7); // lo = 7

    // read/write $2007
    if (lo == 7) {
      tmp = ppubuf;
      if (write) {
        if (V < 8192) {
          if (!rombuf[5]) chrram[get_chr_byte_idx(V)] = val;
        } else if (V < 16128) {
          vram[get_nametable_byte_idx(V)] = val;
        } else {
          palette_ram[toUint8((V & 19) == 16 ? V ^ 16 : V)] = val;
        }
      } else {
        if (V < 8192) {
          ppubuf = get_chr_byte(V);
        } else if (V < 16128) {
          ppubuf = get_nametable_byte(V);
        } else {
          ppubuf = toUint8(palette_ram[toUint8((V & 19) == 16 ? V ^ 16 : V)]);
        }
      }
      if (DBG && !write) printl("V = " + V + ", ppubuf = " + ppubuf);
      V = toUint16(V + (ppuctrl & 4 ? 32 : 1));
      V = toUint16(V % 16384);
      return toUint8(tmp);
    }

    if (write)
      switch (lo) {
      case 0: // $2000 ppuctrl
        ppuctrl = val;
        T = toUint16(T & 62463 | val % 4 << 10);
        break;

      case 1: // $2001 ppumask
        // printl("writing " + val + " to ppumask");
        ppumask = val;
        break;

      case 5: // $2005 ppuscroll
        T = toUint16((W = toUint8(W ^ 1))      ? (fine_x = toUint8(val & 7),
        T & ~31 | val / 8) : T & 35871 | val % 8 << 12 | (val & 248) * 4);
        break;

      case 6: // $2006 ppuaddr
        T = toUint16((W = toUint8(W ^ 1)) ? T & 255 | val % 64 << 8 : (V = toUint16(T & ~255 | val)));
      }

    if (lo == 2) { // $2002 ppustatus
      // the culprit!!!!
      // printl("$2002 ppustatus: " + ppustatus); // is 0, should be 128
      tmp = toUint8(ppustatus & 224);
      ppustatus = toUint8(ppustatus & 127);
      W = 0;
      return tmp;
    }

    break;

  case 4:
    if (write && lo == 20) // $4014 OAM DMA
      for (sum = 256; sum--;)
        oam[sum] = mem(sum, val, 0, 0);
    // $4016 Joypad 1
    for (tmp = 0, hi = 8; hi--;)
      tmp = tmp * 2 + key_state[hi];
    return toUint8((lo == 22) ? write ? keys = tmp : (tmp = toUint8(keys & 1), keys /= 2, tmp)
                      : 0);

  case 6: case 7: // $6000...$7fff PRG RAM
    return toUint8(write ? prgram[a & 8191] = val : prgram[a & 8191]);

  default: // $8000...$ffff ROM
    // handle mmc1 writes
    if (write)
      switch (rombuf[6] >>> 4) {
      case 7: // mapper 7
        mirror = !(val / 16);
        prg[0] = val = toUint8(val % 8 * 2);
        prg[1] = toUint8(val + 1);
        break;

      case 4: // mapper 4
        switch (hi >>> 1) {
          case 4: // Bank select/bank data
            if (a & 1) mmc3_chrprg[mmc3_bits & 7] = val;
            else mmc3_bits = val;
            tmp = toUint8(mmc3_bits >>> 5 & 4);
            for (lo = 4; lo--;) {
              chr[0 + lo + tmp] = toUint8(mmc3_chrprg[lo / 2] & ~!(lo % 2) | lo % 2);
              chr[4 + lo - tmp] = toUint8(mmc3_chrprg[toUint8(2 + lo)]);
            }
            tmp = toUint8(mmc3_bits >>> 5 & 2);
            prg[0 + tmp] = toUint8(mmc3_chrprg[6]);
            prg[1] = toUint8(mmc3_chrprg[7]);
            prg[2 - tmp] = toUint8(rombuf[4] * 2 - 2);
            prg[3] = toUint8(rombuf[4] * 2 - 1);
            break;
          case 5: // Mirroring
            if (toUint8(~a & 1)) {
              mirror = toUint8(2 + (val & 1));
            }
            break;
          case 6:  // IRQ Latch
            if (toUint8(~a & 1)) {
              mmc3_latch = toUint8(val);
            }
            break;
          case 7:  // IRQ Enable
            mmc3_irq = toUint8(a & 1);
            break;
        }
        break;

      case 3: // mapper 3
        chr[0] = val = toUint8(val % 4 * 2);
        chr[1] = toUint8(val + 1);
        break;

      case 2: // mapper 2
        prg[0] = toUint8(val & 31);
        break;

      case 1: // mapper 1
        if (val & 128) {
          mmc1_bits = 5, mmc1_data = 0, mmc1_ctrl = toUint8(mmc1_ctrl | 12);
        } else if (mmc1_data = toUint8(mmc1_data / 2 | val << 4 & 16), !(mmc1_bits = toUint8(mmc1_bits - 1))) {
          mmc1_bits = 5, tmp = toUint8(a >>> 13);
          // (tmp == 4 ? mirror = mmc1_data & 3, mmc1_ctrl
          // : tmp == 5   ? chrbank0
          // : tmp == 6   ? chrbank1
          //             : prgbank) = mmc1_data;
          if (tmp == 4) {
            mirror = toUint8(mmc1_data & 3);
            mmc1_ctrl = toUint8(mmc1_data);
          } else if (tmp == 5) {
            chrbank0 = toUint8(mmc1_data);
          } else if (tmp == 6) {
            chrbank1 = toUint8(mmc1_data);
          } else {
            prgbank = toUint8(mmc1_data);
          }

          // Update CHR banks.
          chr[0] = toUint8(chrbank0 & ~!(mmc1_ctrl & 16));
          chr[1] = toUint8(mmc1_ctrl & 16 ? chrbank1 : chrbank0 | 1);

          // Update PRG banks.
          tmp = toUint8(mmc1_ctrl / 4 & 3);
          prg[0] = toUint8(tmp == 2 ? 0 : tmp == 3 ? prgbank : prgbank & ~1);
          prg[1] = toUint8(tmp == 2 ? prgbank : tmp == 3 ? rombuf[4] - 1 : prgbank | 1);
        }
      }
    return toUint8(rombuf[16 + ((prg[toUint8(hi - 8 >>> prgbits - 12)] & (rombuf[4] << 14 - prgbits) - 1)
                   << prgbits |
               a & (1 << prgbits) - 1)]);
  }

  return toUint8(~0);
}

// Read a byte at address `PCH:PCL` and increment PC.
function read_pc() {
  val = mem(PCL, PCH, 0, 0);
  !(PCL = toUint8(PCL + 1)) ? (PCH = toUint8(PCH + 1)) : 0;
  if (DBG) printl(val + ":" + PCL + ":" + PCH);
  return val;
}

// Set N (negative) and Z (zero) flags of `P` register, based on `val`.
function set_nz(val, src) {
  val = toUint8(val);
  // printl("@" + src + " " + val + ", " + (P & toUint8(~130)) + " | " + (val & 128) + " | " + ((!val).tointeger() * 2));
  if (DBG) printl(val + ", " + (P & toUint8(~130)) + " | " + (val & 128) + " | " + ((!val).tointeger() * 2));
  return P = toUint8(P & toUint8(~130) | val & 128 | (!val).tointeger() * 2);
}

::smolnes_main <- function (rom) {
  // SDL_RWread(SDL_RWFromFile(argv[1], "rb"), rombuf, 1024 * 1024, 1);
  ::rombuf = rom;
  // Start PRG0 after 16-byte header.
  // rom = rombuf + 16;
  // PRG1 is the last bank. `rombuf[4]` is the number of 16k PRG banks.
  prg[1] = toUint8(rombuf[4] - 1);
  // CHR0 ROM is after all PRG data in the file. `rombuf[5]` is the number of
  // 8k CHR banks. If it is zero, assume the game uses CHR RAM.
  // chrrom = rombuf[5] ? rombuf + 16 + ((prg[1] + 1) << 14) : chrram;
  // CHR1 is the last 4k bank.
  chr[1] = toUint8((rombuf[5] ? rombuf[5] : 1) * 2 - 1);
  // Bit 0 of `rombuf[6]` is 0=>horizontal mirroring, 1=>vertical mirroring.
  mirror = (!(rombuf[6] & 1) ? 1 : 0) + 2;
  if (rombuf[6] / 16 == 4) {
    mem(0, 128, 0, 1); // Update to default mmc3 banks
    prgbits = toUint8(prgbits - 1);         // 8kb PRG banks
    chrbits = toUint8(chrbits - 2);      // 1kb CHR banks
  }

  // Start at address in reset vector, at $FFFC.
  PCL = mem(~3, ~0, 0, 0);
  PCH = mem(~2, ~0, 0, 0);

  while (true) {
    cycles = nomem = 0;

    if (nmi_irq) goto <- "nmi_irq";

    if (!goto) {
      opcode = read_pc(); // 76
      // printl(opcode);
    } else {
      // printl(goto);
    }

    if (goto == "nmi_irq") {
      goto = null;
      mem(S, 1, PCH, 1); S = toUint8(S - 1);
      mem(S, 1, PCL, 1); S = toUint8(S - 1);
      mem(S, 1, P | 32, 1); S = toUint8(S - 1);
      // BRK/IRQ vector is $ffff, NMI vector is $fffa
      PCL = mem(~1 - (nmi_irq & 4), ~0, 0, 0);
      PCH = mem(~0 - (nmi_irq & 4), ~0, 0, 0);
      nmi_irq = 0;
      cycles = toUint16(cycles + 1);
      cycles = toUint16(cycles + 4);
    } else switch (opcode & 31) { // 13
    case 0:
      if (!goto) {
        if (opcode & 128) { // LDY/CPY/CPX imm
          read_pc();
          nomem = 1;
          goto <- "nomemop";
        }
      }

      switch (opcode >>> 5) {
      case 0: // BRK or nmi_irq
        if (!goto) !(PCL = toUint8(PCL + 1)) ? (PCH = toUint8(PCH + 1)) : 0;
      // nmi_irq:
      if (goto == "nmi_irq") goto = null;
      if (!goto) {
        mem(S, 1, PCH, 1); S = toUint8(S - 1);
        mem(S, 1, PCL, 1); S = toUint8(S - 1);
        mem(S, 1, P | 32, 1); S = toUint8(S - 1);
        // BRK/IRQ vector is $ffff, NMI vector is $fffa
        PCL = mem(~1 - (nmi_irq & 4), ~0, 0, 0);
        PCH = mem(~0 - (nmi_irq & 4), ~0, 0, 0);
        nmi_irq = 0;
        cycles = toUint16(cycles + 1);
        break;
      }

      case 1: // JSR
        if (!goto) {
          result = toUint8(read_pc());
          mem(S, 1, PCH, 1); S = toUint8(S - 1);
          mem(S, 1, PCL, 1); S = toUint8(S - 1);
          PCH = read_pc();
          PCL = result;
          break;
        }

      case 2: // RTI
        if (!goto) {
          P = toUint8(mem(S = toUint8(S + 1), 1, 0, 0) & ~32);
          PCL = mem(S = toUint8(S + 1), 1, 0, 0);
          PCH = mem(S = toUint8(S + 1), 1, 0, 0);
          break;
        }

      case 3: // RTS
        if (!goto) {
          PCL = mem(S = toUint8(S + 1), 1, 0, 0);
          PCH = mem(S = toUint8(S + 1), 1, 0, 0);
          !(PCL = toUint8(PCL + 1)) ? (PCH = toUint8(PCH + 1)) : 0;
          break;
        }
      }

      if (!goto) cycles = toUint16(cycles + 4);
      if (!goto) break;

    case 16: // BPL, BMI, BVC, BVS, BCC, BCS, BNE, BEQ
      if (!goto) {
        read_pc();
        if (DBG) {
          printl("P: " + P);
          printl("opcode >>> 6 & 3: " + (opcode >>> 6 & 3));
          printl("mask: " + mask[opcode >>> 6 & 3]);
        }
        // printl("check: " + ((!toUint8(P & mask[toUint8(opcode >>> 6) & 3])).tointeger() ^ opcode / 32 & 1));
        if ((!toUint8(P & mask[toUint8(opcode >>> 6) & 3])).tointeger() ^ opcode / 32 & 1) {
          if (DBG) printl("check: 1");
          // printl("cross: " + (toUint8(PCL + toInt8(val) >>> 8)));
          if (cross = toUint8(PCL + toInt8(val) >>> 8)) {
            PCH = toUint8(PCH + cross);
            cycles = toUint16(cycles + 1);
          }
          cycles = toUint16(cycles + 1), PCL = toUint8(PCL + toInt8(val));
        }
        break;
      }

    case 8:
    case 8 + 16:

      if (!goto) {switch (opcode = toUint8(opcode >>> 4)) {
      case 0: // PHP
        mem(S, 1, P | 48, 1); S = toUint8(S - 1);
        cycles = toUint16(cycles + 1);
        break;

      case 2: // PLP
        P = toUint8(mem(S = toUint8(S + 1), 1, 0, 0) & ~16);
        cycles = toUint16(cycles + 2);
        break;

      case 4: // PHA
        mem(S, 1, A, 1); S = toUint8(S - 1);
        cycles = toUint16(cycles + 1);
        break;

      case 6: // PLA
        set_nz(A = mem(S = toUint8(S + 1), 1, 0, 0), "PLA");
        cycles = toUint16(cycles + 2);
        break;

      case 8: // DEY
        set_nz(Y = toUint8(Y - 1), "DEY");
        break;

      case 9: // TYA
        set_nz(A = Y, "TYA");
        break;

      case 10: // TAY
        set_nz(Y = A, "TAY");
        break;

      case 12: // INY
        set_nz(Y = toUint8(Y + 1), "INY");
        break;

      case 14: // INX
        set_nz(X = toUint8(X + 1), "INX");
        break;

      default: // CLC, SEC, CLI, SEI, CLV, CLD, SED
        P = toUint8(P & ~mask[opcode + 3] | mask[opcode + 4]);
        break;
      }
      break;
    }

    case 10:
    case 10 + 16:

      if (!goto) {
        switch (opcode >>> 4) {
          case 8: // TXA
            set_nz(A = X, "TXA");
            break;

          case 9: // TXS
            S = X;
            break;

          case 10: // TAX
            set_nz(X = A, "TAX");
            break;

          case 11: // TSX
            set_nz(X = S, "TSX");
            break;

          case 12: // DEX
            set_nz(X = toUint8(X - 1), "DEX");
            break;

          case 14: // NOP
            break;

          default: // ASL/ROL/LSR/ROR A
            nomem = 1;
            val = A;
            goto <- "nomemop";
        }
        if (!goto) break;
    }

    case 1: // X-indexed, indirect
      if (!goto) {
        read_pc();
        val = toUint8(val + X);
        addr_lo = mem(val, 0, 0, 0);
        addr_hi = mem(val + 1, 0, 0, 0);
        cycles = toUint16(cycles + 4);
        goto <- "opcode";
      }

    case 4: case 5: case 6: // Zeropage
      if (!goto) {
        addr_lo = read_pc();
        addr_hi = 0;
        cycles = toUint16(cycles + 1);
        goto <- "opcode";
      }

    case 2: case 9: // Immediate
      if (!goto) {
        read_pc();
        nomem = 1;
        goto <- "nomemop";
      }

    case 12: case 13: case 14: // Absolute
      if (!goto) {
        addr_lo = read_pc(); // 7
        addr_hi = read_pc(); // 32
        cycles = toUint16(cycles + 2);
        goto <- "opcode";
      }

    case 17: // Zeropage, Y-indexed
      if (!goto) {
        addr_lo = mem(read_pc(), 0, 0, 0);
        addr_hi = mem(val + 1, 0, 0, 0);
        val = Y;
        tmp = opcode == 145; // STA always uses extra cycle.
        cycles = toUint16(cycles + 1);
        goto <- "cross";
      }

    case 20: case 21: case 22: // Zeropage, X-indexed
      if (!goto) {
        addr_lo = toUint8(read_pc() + ((opcode & 214) == 150 ? Y : X)); // LDX/STX use Y
        addr_hi = 0;
        cycles = toUint16(cycles + 2);
        goto <- "opcode";
      }

    case 25: // Absolute, Y-indexed.
      if (!goto) {
        addr_lo = read_pc(); // 251
        addr_hi = read_pc(); // 2
        val = Y;
        tmp = opcode == 153; // STA always uses extra cycle.
        goto <- "cross";
      }

    case 28: case 29: case 30: // Absolute, X-indexed.
      if (!goto) {
        addr_lo = read_pc(); // 215
        addr_hi = read_pc(); // 7
        val = opcode == 190 ? Y : X; // LDX uses Y
        tmp = opcode == 157 ||      // STA always uses extra cycle.
                                // ASL/ROL/LSR/ROR/INC/DEC all uses extra cycle.
              opcode % 16 == 14 && opcode != 190;
        // fallthrough
      }
    // cross:
    if (goto == "cross") goto = null;
    if (!goto) {
      cross = (addr_lo + val > 255).tointeger();
      addr_hi = toUint8(addr_hi + cross);
      addr_lo = toUint8(addr_lo + val);
      // printl(cycles + " + 2 + " + tmp.tointeger() + " | " + cross);
      // local cycles_pre = cycles;
      cycles = toUint16(cycles + (2 + tmp.tointeger() | cross));
      // printl("cycles @cross: " + cycles_pre + ", " + cycles);
      // fallthrough
    }

    // opcode:
    if (goto == "opcode") goto = null;
    if (!goto) {
      // Read from the given address into `val` for convenience below, except
      // for the STA/STX/STY instructions, and JMP.
      if ((opcode & 224) != 128 && opcode != 76) {
        local val_pre = val; // 32
        // val = mem(7, 32, 0, 0);
        val = mem(addr_lo, addr_hi, 0, 0); // is 0, should be 32
        if (DBG) printl("1: " + val_pre + ", 2: " + val);
      }
    }

    // nomemop:
    if (goto == "nomemop") goto = null;
    if (!goto) {switch (opcode & 243) { // 64
      case 1:
      case 1 + 16:
      set_nz(A = toUint8(A | val), "ORA");  // ORA
      break;
      case 33:
      case 33 + 16:
      set_nz(A = toUint8(A & val), "AND"); // AND
      break;
      case 65:
      case 65 + 16:
      set_nz(A = toUint8(A ^ val), "EOR"); // EOR

      break;
      case 225:
      case 225 + 16:
      // SBC
        val = toUint8(~val);
        goto <- "add";

      case 97:
      case 97 + 16:
      // ADC
      // add:
      if (goto == "add") goto = null;
      if (!goto) {
        sum = toUint16(A + val + (P & 1));
        P = toUint8(P & ~65 | (sum > 255).tointeger() | (~(A ^ val) & (val ^ sum) & 128) / 2);
        set_nz(A = toUint8(sum), "ADC");
        break;
      }

      case 2:
      case 2 + 16:
      // ASL
      if (!goto) {
        result = toUint8(val * 2);
        P = toUint8(P & ~1 | val / 128);
        goto <- "memop";
      }

      case 34:
      case 34 + 16:
      // ROL
      if (!goto) {
        result = toUint8(val * 2 | P & 1);
        P = toUint8(P & ~1 | val / 128);
        goto <- "memop";
      }

      case 66:
      case 66 + 16:
      // LSR
      if (!goto) {
        result = toUint8(val / 2);
        P = toUint8(P & ~1 | val & 1);
        goto <- "memop";
      }

      case 98:
      case 98 + 16:
      // ROR
      if (!goto) {
        result = toUint8(val / 2 | toUint8(P << 7));
        P = toUint8(P & ~1 | val & 1);
        goto <- "memop";
      }

      case 194:
      case 194 + 16:
      // DEC
      if (!goto) {
        result = toUint8(val - 1);
        goto <- "memop";
      }

      case 226:
      case 226 + 16:
      // INC
        if (!goto) result = toUint8(val + 1);
        // fallthrough

      // memop:
      if (goto == "memop") goto = null;
      if (!goto) {
        set_nz(result, "MEMOP");
        // Write result to A or back to memory.
        nomem ? A = toUint8(result) : (cycles = toUint16(cycles + 2), mem(addr_lo, addr_hi, result, 1));
        break;
      }

      case 32: // BIT
        P = toUint8(P & 61 | val & 192 | (!(A & val)).tointeger() * 2);
        break;

      case 64: // JMP
        PCL = toUint8(addr_lo); // 87
        PCH = toUint8(addr_hi); // 128
        cycles = toUint16(cycles - 1);
        break;

      case 96: // JMP indirect
        PCL = toUint8(val);
        PCH = mem(addr_lo + 1, addr_hi, 0, 0);
        cycles = toUint16(cycles + 1);

      break;
      case 160:
      case 160 + 16:
      set_nz(Y = toUint8(val), "LDY"); // LDY
      break;
      case 161:
      case 161 + 16:
      set_nz(A = toUint8(val), "LDA"); // LDA
      break;
      case 162:
      case 162 + 16:
      set_nz(X = toUint8(val), "LDX"); // LDX

      break;
      case 128:
      case 128 + 16:
      result = Y; goto <- "store"; // STY
      if (!goto) break;
      case 129:
      case 129 + 16:
      if (!goto) {result = A; goto <- "store";} // STA
      if (!goto) break;
      case 130:
      case 130 + 16:
      if (!goto) result = X;             // STX

      // store:
      if (goto == "store") goto = null;
      if (!goto) {
        mem(addr_lo, addr_hi, result, 1);
        break;
      }
      case 192:
      case 192 + 16:
      result = Y; goto <- "cmp"; // CPY
      if (!goto) break;
      case 193:
      case 193 + 16:
      if (!goto) {result = A; goto <- "cmp";} // CMP
      if (!goto) break;
      case 224:
      case 224 + 16:
      if (!goto) result = X;           // CPX
      // cmp:
      if (goto == "cmp") goto = null;
      if (!goto) {
        P = toUint8(P & ~1 | (result >= val).tointeger());
        set_nz(toUint8(result - val), "CMP");
        break;
      }
      }}
    }

    // Update PPU, which runs 3 times faster than CPU. Each CPU instruction
    // takes at least 2 cycles.
    if (DBG) printl("PPU start cycle: " + toUint8(cycles * 3 + 6));
    for (tmp = toUint8(cycles * 3 + 6); tmp--;) {

      // printl("Dot: " + dot + ", Scany: " + scany + ", Color: " + color + ", Palette: " + palette);
      // printl("Dot: " + dot + ", Scany: " + scany + ", BG/Sprites: " + (ppumask & 24));

      if (ppumask & 24) { // If background or sprites are enabled.
        // printl("UPDATING FRAMEBUFFER");
        if (scany < 240) {
          if (dot < 256 || dot > 319) {
            switch (dot & 7) {
            case 1: // Read nametable byte.
              ntb = get_nametable_byte(V);
              break;
            case 3: // Read attribute byte.
              atb = toUint16((get_nametable_byte(960 | V & 3072 | V >>> 4 & 56 |
                                        V / 4 & 7) >>>
                    (V >>> 5 & 2 | V / 2 & 1) * 2) %
                    4 * 0x5555);
              break;
            case 5: // Read pattern table low byte.
              ptb_lo = get_chr_byte(ppuctrl << 8 & 4096 | ntb << 4 | V >>> 12);
              break;
            case 7: // Read pattern table high byte.
              ptb_hi =
                  get_chr_byte(ppuctrl << 8 & 4096 | ntb << 4 | V >>> 12 | 8);
              // Increment horizontal VRAM read address.
              V = toUint16((V & 31) == 31 ? V & ~31 ^ 1024 : V + 1);
              break;
            }

            // Draw a pixel to the framebuffer.
            if (scany < 240 && dot < 256) {
              // Read color and palette from shift registers.
              local color = toUint8(shift_hi >>> 14 - fine_x & 2 |
                              shift_lo >>> 15 - fine_x & 1),
                      palette = toUint8(shift_at >>> 28 - fine_x * 2 & 12);

              // If sprites are enabled.
              if (ppumask & 16)
                // Loop through all sprites.
                for (local sprite = 0; sprite < 256; sprite += 4) {
                  local sprite_h = toUint16(ppuctrl & 32 ? 16 : 8),
                          sprite_x = toUint16(dot - oam[sprite + 3]),
                          sprite_y = toUint16(scany - oam[sprite] - 1),
                          sx = toUint16(sprite_x ^ (oam[sprite + 2] & 64 ? 0 : 7)),
                          sy = toUint16(sprite_y ^ (oam[sprite + 2] & 128 ? sprite_h - 1 : 0));
                  if (sprite_x < 8 && sprite_y < sprite_h) {
                    local sprite_tile = toUint16(oam[sprite + 1]),
                            sprite_addr = toUint16(ppuctrl & 32
                                              // 8x16 sprites
                                              ? sprite_tile % 2 << 12 |
                                                    (sprite_tile & ~1) << 4 |
                                                    (sy & 8) * 2 | sy & 7
                                              // 8x8 sprites
                                              : (ppuctrl & 8) << 9 |
                                                    sprite_tile << 4 | sy & 7),
                            sprite_color = toUint16(
                                get_chr_byte(sprite_addr + 8) >>> sx << 1 & 2 |
                                get_chr_byte(sprite_addr) >>> sx & 1);
                    // Only draw sprite if color is not 0 (transparent)
                    if (sprite_color) {
                      // Don't draw sprite if BG has priority.
                      if (!(oam[sprite + 2] & 32 && color)) {
                        color = toUint8(sprite_color);
                        palette = toUint8(16 | oam[sprite + 2] * 4 & 12);
                      }
                      // Maybe set sprite0 hit flag.
                      sprite == 0 &&color ? ppustatus = toUint8(ppustatus | 64) : 0;
                      break; // goto found_sprite;
                    }
                  }
                }
            // found_sprite:

              // Write pixel to framebuffer. Always use palette 0 for color 0.
              // BGR565 palette is used instead of RGBA32 to reduce source code
              // size.
              frame_buffer[scany * 256 + dot] =
                    ([25356, 34816, 39011, 30854, 24714, 4107,  106,   2311,
                      2468,  2561,  4642,  6592,  20832, 0,     0,     0,
                      44373, 49761, 55593, 51341, 43186, 18675, 434,   654,
                      4939,  5058,  3074,  19362, 37667, 0,     0,     0,
                      65535,    64716,  64497, 64342, 62331, 43932, 23612, 9465,
                      1429,  1550,  20075, 36358, 52713, 16904, 0,     0,
                      65535,    65207,  65113,  65083,  65053,  58911, 50814, 42620,
                      40667, 40729, 48951, 53078, 61238, 44405])[palette_ram[color ? palette | color : 0]];
            }

            // Update shift registers every cycle.
            if (dot < 336) {
              shift_hi = toUint16(shift_hi * 2);
              shift_lo = toUint16(shift_lo * 2);
              shift_at = toUint16(shift_at * 4);
            }

            // Reload shift registers every 8 cycles.
            if (dot % 8 == 7) {
              shift_hi = toUint16(shift_hi | ptb_hi);
              shift_lo = toUint16(shift_lo | ptb_lo);
              shift_at = toUint16(shift_at | atb);
            }
          }

          // Increment vertical VRAM address.
          dot == 256 ? V = ((V & 7 << 12) != 7 << 12 ? V + 4096
                            : (V & 992) == 928       ? V & 35871 ^ 2048
                            : (V & 992) == 992       ? V & 35871
                                              : V & 35871 | V + 32 & 992) &
                              // Reset horizontal VRAM address to T value.
                              ~1055 |
                          T & 1055
                    : 0;
          if (dot == 261 && mmc3_irq && !mmc3_latch) nmi_irq = 1;
          mmc3_latch = toUint8(mmc3_latch - 1);
        }

        // Reset vertical VRAM address to T value.
        scany == 261 &&dot > 279 &&dot < 305 ? V = toUint16(V & 33823 | T & 31712) : 0;
      }

      if (scany == 241 && dot == 1) {
        // If NMI is enabled, trigger NMI.
        ppuctrl & 128 ? (nmi_irq = 4) : 0;
        ppustatus = toUint8(ppustatus | 128);

        // TODO: RENDER FRAME

        if (DBG) printl("RENDERING FRAME!!");
        // for (local i = 10; i < 20; i ++) {
        //   for (local j = 10; j < 40; j ++) {
        //     print(frame_buffer[i * 240 + j]);
        //   }
        //   print("\n");
        // }

      } else {
        // printl("scany: " + scany + ", dot: " + dot);
      }

      // Clear ppustatus.
      scany == 261 &&dot == 1 ? ppustatus = 0 : 0;

      // Increment to next dot/scany. 341 dots per scanline, 262 scanlines per
      // frame. Scanline 261 is represented as -1.
      if (++dot == 341) {
        dot = 0;
        scany = toUint16(scany + 1);
        scany = toUint16(scany % 262);
      }
    }
  }
}
