package hardfloat.test

import java.text.SimpleDateFormat
import java.util.Calendar
import scala.collection.mutable.ArrayBuffer
import scala.collection.parallel.CollectionConverters._

/** Dedicated testbench for AddRecFN(6, 6) with statically computed test cases
  * covering all exponent-alignment distances, close/far paths, cancellation,
  * subnormals, overflow/underflow, rounding modes, and special values.
  */
class AddRecF6_6Spec extends FMATester {
  private val expWidth = 6
  private val sigWidth = 6
  private val bias = (1 << (expWidth - 1)) - 1 // 31
  private val maxExp = (1 << expWidth) - 1      // 63
  private val fracMask = (1 << (sigWidth - 1)) - 1 // 0x1F
  private val canonNaN = (maxExp << (sigWidth - 1)) | (1 << (sigWidth - 2)) // 0x7F0

  private case class Unpacked(
    sign: Boolean,
    exp: Int,
    frac: Int,
    sig: Int,
    lsbExp: Int,
    isZero: Boolean,
    isInf: Boolean,
    isNaN: Boolean,
    isSNaN: Boolean
  )

  private def unpack(bits: Int): Unpacked = {
    val sign = ((bits >> (expWidth + sigWidth - 1)) & 1) != 0
    val exp = (bits >> (sigWidth - 1)) & maxExp
    val frac = bits & fracMask
    val isZero = exp == 0 && frac == 0
    val isInf = exp == maxExp && frac == 0
    val isNaN = exp == maxExp && frac != 0
    val isSNaN = isNaN && ((frac & (1 << (sigWidth - 2))) == 0)
    val sig = if (exp == 0) frac else (1 << (sigWidth - 1)) | frac
    val lsbExp = (if (exp == 0) 1 else exp) - bias - (sigWidth - 1)
    Unpacked(sign, exp, frac, sig, lsbExp, isZero, isInf, isNaN, isSNaN)
  }

  private def pack(sign: Boolean, exp: Int, frac: Int): Int = {
    ((if (sign) 1 else 0) << (expWidth + sigWidth - 1)) |
      ((exp & maxExp) << (sigWidth - 1)) |
      (frac & fracMask)
  }

  private def computeExpected(aBits: Int, bBits: Int, roundingMode: Int, detectTininess: Int): (Int, Int) = {
    val a = unpack(aBits)
    val b = unpack(bBits)

    if (a.isNaN || b.isNaN) {
      val invalid = if (a.isSNaN || b.isSNaN) 0x10 else 0x00
      return (canonNaN, invalid)
    }
    if (a.isInf && b.isInf) {
      if (a.sign != b.sign) return (canonNaN, 0x10)
      return (pack(a.sign, maxExp, 0), 0x00)
    }
    if (a.isInf) return (pack(a.sign, maxExp, 0), 0x00)
    if (b.isInf) return (pack(b.sign, maxExp, 0), 0x00)
    if (a.isZero && b.isZero) {
      val outSign = if (a.sign == b.sign) a.sign else roundingMode == 2
      return (pack(outSign, 0, 0), 0x00)
    }

    val minExp = math.min(a.lsbExp, b.lsbExp)
    val termA = (if (a.sign) -BigInt(a.sig) else BigInt(a.sig)) << (a.lsbExp - minExp)
    val termB = (if (b.sign) -BigInt(b.sig) else BigInt(b.sig)) << (b.lsbExp - minExp)
    val sum = termA + termB

    if (sum == 0) {
      return (pack(roundingMode == 2, 0, 0), 0x00)
    }

    val outSign = sum < 0
    val mag = sum.abs
    val trueExp = minExp + (mag.bitLength - 1)
    val minNormalExp = 1 - bias // -30
    val minLsbExp = minNormalExp - (sigWidth - 1) // -35

    def roundAt(targetLsbExp: Int): (BigInt, Boolean) = {
      val shift = targetLsbExp - minExp
      if (shift <= 0) {
        (mag << (-shift), false)
      } else {
        val q = mag >> shift
        val rem = mag & ((BigInt(1) << shift) - 1)
        val half = BigInt(1) << (shift - 1)
        val inexact = rem != 0
        val inc = roundingMode match {
          case 0 => rem > half || (rem == half && q.testBit(0)) // near_even
          case 1 => false                                         // minMag
          case 2 => outSign && inexact                            // min
          case 3 => !outSign && inexact                           // max
          case 4 => rem >= half                                   // near_maxMag
          case 6 => inexact && !q.testBit(0)                      // odd (jam)
        }
        (if (inc) q + 1 else q, inexact)
      }
    }

    // Tininess check: before rounding (0) or after rounding with unbounded exponent (1)
    val tiny = if (detectTininess == 0) {
      trueExp < minNormalExp
    } else {
      val (unboundedQ, _) = roundAt(trueExp - (sigWidth - 1))
      val roundedExp = if (unboundedQ == (BigInt(1) << sigWidth)) trueExp + 1 else trueExp
      roundedExp < minNormalExp
    }

    val targetLsbExp = math.max(trueExp - (sigWidth - 1), minLsbExp)
    val (qInit, inexact) = roundAt(targetLsbExp)

    var normExp = if (trueExp >= minNormalExp) trueExp + bias else 0
    var q = qInit
    if (trueExp >= minNormalExp && q == (BigInt(1) << sigWidth)) {
      q = BigInt(1) << (sigWidth - 1)
      normExp += 1
    } else if (trueExp < minNormalExp && q == (BigInt(1) << (sigWidth - 1))) {
      normExp = 1
    }

    if (normExp >= maxExp) {
      val overflowToInf = roundingMode match {
        case 0 | 4 => true
        case 1 | 6 => false
        case 2     => outSign
        case 3     => !outSign
      }
      val outBits = if (overflowToInf) pack(outSign, maxExp, 0) else pack(outSign, maxExp - 1, fracMask)
      val flags = 0x04 | 0x01 // overflow | inexact
      (outBits, flags)
    } else {
      val underflow = tiny && inexact
      val flags = (if (underflow) 0x02 else 0x00) | (if (inexact) 0x01 else 0x00)
      (pack(outSign, normExp, q.toInt & fracMask), flags)
    }
  }

  private lazy val inputPairs: Seq[(Int, Int)] = {
    val pairs = ArrayBuffer.empty[(Int, Int)]

    // 1. All alignment distances delta in [-18, 18] plus large max-align deltas
    val baseExps = Seq(0, 1, 10, 31, 48, 62)
    val deltas = (-18 to 18) ++ Seq(-35, -25, 25, 35)
    val fracs = Seq(0x00, 0x01, 0x0a, 0x10, 0x15, 0x1f)
    for {
      expA <- baseExps
      delta <- deltas
      expB = expA - delta if expB >= 0 && expB <= 62
      fA <- fracs
      fB <- fracs
      sA <- Seq(false, true)
      sB <- Seq(false, true)
    } {
      pairs += ((pack(sA, expA, fA), pack(sB, expB, fB)))
    }

    // 2. Exhaustive close-path cancellation & subnormal transitions (|delta| <= 1)
    for {
      expA <- Seq(0, 1, 2, 31)
      expB <- Seq(expA - 1, expA, expA + 1) if expB >= 0 && expB <= 62
      fA <- 0 to fracMask
      fB <- 0 to fracMask
    } {
      pairs += ((pack(false, expA, fA), pack(true, expB, fB)))
      pairs += ((pack(false, expA, fA), pack(false, expB, fB)))
    }

    // 3. Special values (zeros, subnormals, max normal, +/-Inf, qNaN, sNaN)
    val specials = Seq(
      0x000, 0x800, // +0, -0
      0x001, 0x801, // +minSubnorm, -minSubnorm
      0x01f, 0x81f, // +maxSubnorm, -maxSubnorm
      0x020, 0x820, // +minNorm, -minNorm
      0x3e0, 0xbe0, // +1.0, -1.0
      0x7df, 0xfdf, // +maxNorm, -maxNorm
      0x7e0, 0xfe0, // +Inf, -Inf
      0x7f0, 0xff0, // qNaN
      0x7e1, 0xfe1  // sNaN
    )
    for (a <- specials; b <- specials) {
      pairs += ((a, b))
    }

    pairs.distinct.toSeq
  }

  "AddRecF6_6" should "pass" in {
    val name = "AddRecF6_6"
    val testRunDir =
      os.pwd / "test_run_dir" / s"${this.getClass.getSimpleName}_$name" /
        s"${new SimpleDateFormat("yyyyMMddHHmmss").format(Calendar.getInstance.getTime)}"
    os.makeDir.all(testRunDir)
    os.write(testRunDir / "dut.v", chisel3.getVerilogString(new ValExec_AddRecFN(expWidth, sigWidth)))

    val verilatorCompile = Seq(
      "verilator",
      "-cc",
      "--prefix", "dut",
      "--Mdir", testRunDir.toString,
      "-CFLAGS", s"""-I${getClass.getResource("/includes/").getPath} -include ${getClass.getResource(s"/includes/$name.h").getPath}""",
      "dut.v",
      "--exe", s"${getClass.getResource("/csrc/test.cpp").getPath}"
    )
    os.proc(verilatorCompile).call(testRunDir)
    os.proc("make", "-C", testRunDir.toString, "-j", "-f", "dut.mk", "dut").call(testRunDir)

    val configs = for {
      (rName, rCode) <- roundings
      tCode <- Seq("0", "1")
    } yield (rName, rCode, tCode)

    val stdouts = configs.par.map { case (rName, rCode, tCode) =>
      val rm = rCode.toInt
      val dt = tCode.toInt
      val sb = new StringBuilder(inputPairs.size * 16)
      for ((a, b) <- inputPairs) {
        val (out, flags) = computeExpected(a, b, rm, dt)
        sb.append(f"$a%03x $b%03x $out%03x $flags%02x\n")
      }
      val stdoutFile = testRunDir / s"${name}__${rName}_t${tCode}.txt"
      os.proc((testRunDir / "dut").toString, rCode, tCode)
        .call(stdin = sb.toString, stdout = stdoutFile)
      os.read(stdoutFile)
    }.seq

    check(stdouts)
  }
}

