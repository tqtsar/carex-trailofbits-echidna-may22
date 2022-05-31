// SPDX-License-Identifier: BSD-4-Clause
pragma solidity ^0.8.1;

import "ABDKMath64x64.sol";

contract Test {
   int128 internal zero = ABDKMath64x64.fromInt(0);
   int128 internal one = ABDKMath64x64.fromInt(1);
   int128 private constant MIN_64x64 = -0x80000000000000000000000000000000;
   int128 private constant MAX_64x64 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

   event Value(string, int128);

   function debug(string calldata x, int128 y) public {
     emit Value(x, ABDKMath64x64.toInt(y));
   }

   function abs256(int256 x) public returns (int256) {
     if(x >= 0)
      return x;
     else
      return -x;
   }

   function minmax(int128 a, int128 b) public returns (int128 min, int128 max) {
     if (a > b) {
       max = a;
       min = b;
     }
     else {
       min = a;
       max = b;
     }
   }

  // ABDKMath64x64 conversion function wrappers

   function fromInt(int256 x) public returns (int128) {
     return ABDKMath64x64.fromInt(x);
   }

   function toInt(int128 x) public returns (int64) {
     return ABDKMath64x64.toInt(x);
   }

   function fromUInt(uint256 x) public returns (int128) {
     return ABDKMath64x64.fromUInt(x);
   }

   function toUInt(int128 x) public returns (uint64) {
     return ABDKMath64x64.toUInt(x);
   }

   function from128x128(int256 x) public returns (int128) {
     return ABDKMath64x64.from128x128(x);
   }

   function to128x128(int128 x) public returns (int256) {
     return ABDKMath64x64.to128x128(x);
   }

   // ABDKMath64x64 arithmetic function wrappers
 
   function add(int128 x, int128 y) public returns (int128) {
     return ABDKMath64x64.add(x, y);
   }

   function sub(int128 x, int128 y) public returns (int128) {
     return ABDKMath64x64.sub(x, y);
   }

   function mul(int128 x, int128 y) public returns (int128) {
     return ABDKMath64x64.mul(x, y);
   }

   function muli(int128 x, int256 y) public returns (int256) {
     return ABDKMath64x64.muli(x, y);
   }

   function mulu(int128 x, uint256 y) public returns (uint256) {
     return ABDKMath64x64.mulu(x, y);
   }

   function div(int128 x, int128 y) public returns (int128) {
     return ABDKMath64x64.div(x, y);
   }

   function divi(int128 x, int256 y) public returns (int256) {
     return ABDKMath64x64.divi(x, y);
   }

   function divu(uint256 x, uint256 y) public returns (int128) {
     return ABDKMath64x64.divu(x, y);
   }

   function neg(int128 x) public returns (int128) {
     return ABDKMath64x64.neg(x);
   }

   function abs(int128 x) public returns (int128) {
     return ABDKMath64x64.abs(x);
   }

   function inv(int128 x) public returns (int128) {
     return ABDKMath64x64.inv(x);
   }

   function avg(int128 x, int128 y) public returns (int128) {
     return ABDKMath64x64.avg(x, y);
   }

   function gavg(int128 x, int128 y) public returns (int128) {
     return ABDKMath64x64.gavg(x, y);
   }

   function pow(int128 x, uint256 y) public returns (int128) {
     return ABDKMath64x64.pow(x, y);
   }

   function sqrt(int128 x) public returns (int128) {
     return ABDKMath64x64.sqrt(x);
   }

   function log_2(int128 x) public returns (int128) {
     return ABDKMath64x64.log_2(x);
   }

   function ln(int128 x) public returns (int128) {
     return ABDKMath64x64.ln(x);
   }

   function exp_2(int128 x) public returns (int128) {
     return ABDKMath64x64.exp_2(x);
   }

   function exp(int128 x) public returns (int128) {
     return ABDKMath64x64.exp(x);
   }



   // Addition function tests

   function testAdd_commutative(int128 x, int128 y) public {
     // Test commutativity
     assert(add(x, y) == add(y, x));
   }

   function testAdd_associative(int128 x, int128 y, int128 z) public {
     // Test associativity
     assert(add(add(x,y), z) == add(x, add(y, z)));
   }

   function testAdd_neutral(int128 x) public {
     // Test for neutral operations
     assert(add(x, zero) == x);
     assert(add(x, neg(x)) == 0);
   }

   function testAdd_overflow(int128 x, int128 y) public {
     int256 res = x + y;

     // Test revert on overflow
     if(res > MAX_64x64 || res < MIN_64x64) {
       try this.add(x,y) { assert(false); } catch {}
     }
   }

   function testAdd_logic(int128 x, int128 y) public {
     int128 res = add(x, y);

     // Both positive, result should be greater than x and y
     if(x >= zero && y >= zero) {
       assert(res >= x && res >= y);
     }
     // Both negative, result should be less than x and y
     if(x < zero && y < zero) {
       assert(res < x && res < y);
     }
     // One positive, one negative. 
     // Result should be less than the biggest, and more than the smallest
     if(x >= zero && y < zero) {
       assert(res < x && res >= y);
     }
     if(x < zero && y >= zero) {
       assert(res < y && res >= x);
     }
   }



  // Subtraction function tests

   function testSub_commutative(int128 x, int128 y) public {
     // Subtraction is not commutative, however we can assert that:
     // a - b == -( b - a )
     assert(sub(x, y) == neg(sub(y, x)));
   }

   function testSub_neutral(int128 x) public {
     // Test for neutral operations
     assert(sub(x, zero) == x);
     assert(sub(x, x) == zero);
   }

   function testSub_overflow(int128 x, int128 y) public {
     int256 res = x - y;

     // Test revert on overflow
     if(res > MAX_64x64 || res < MIN_64x64) {
       try this.sub(x,y) { assert(false); } catch {}
     }
   }

   function testSub_equivalence_to_addition(int128 x, int128 y) public {
     // Subtraction is equivalent to addition, with the second operator negative:
     // a - b == a + (-b)
     assert(sub(x, y) == add(x, neg(y)));
   }

   function testSub_logic(int128 x, int128 y) public {
     int128 res = sub(x, y);

     // If y is greater than x, result is negative
     if(y > x) {
       assert(res < zero);
     }
     // If x is negative, and y is positive, result is negative
     if(x < zero && y >= zero) {
       assert(res < zero);
     }
   }

   // Multiplication functions tests
   
   function testMul_commutative(int128 x, int128 y) public {
     // Fixed point multiplication is commutative, there should be no issue here
     assert(mul(x, y) == mul(y, x));
   }

   function testMul_associative(int128 x, int128 y, int128 z) public {
     int128 xy_z = mul(mul(x,y), z);
     int128 x_yz = mul(x, mul(y,z));

     // This is actually zero, not the 64x64 representation of zero.
     // If any of the two values is zero, it means we lost all precision.
     require(xy_z > 0 && x_yz > 0);

     // We calculate the log2 of the error, as the sum of the log2 of the
     // values to be multiplied. 
     int128 lxyz = add(log_2(x), add(log_2(y), log_2(z)));

     // The result should be between 2**64 and 2**-64
     require(lxyz > fromInt(-64) && lxyz < fromInt(64));

     // The error should be less than 2**lxyz
     assert(abs(sub(xy_z, x_yz)) < exp_2(lxyz));

   }

   function testMul_overflow(int128 x, int128 y) public {
     int256 res = int256(x) * y >> 64;

     // Test revert on overflow
     if(res > MAX_64x64 || res < MIN_64x64) {
       try this.mul(x, y) { assert(false); } catch {}
     }
   }

   function testMul_identity(int128 x) public {
     int128 lx = toInt(log_2(x));
     int128 lix = toInt(log_2(inv(x)));

     // Division (and inverse) loses precision, so we need to find the boundary value
     // for the expected error, in exponent:
     int128 expected_error_order = abs(lx - lix) + 1;

     // The boundary for the error is 2**(-64 + expected_error_order)
     assert(one - mul(x, inv(x)) < exp_2( add(fromInt(-64), fromInt(expected_error_order)) ));
   }

   function testMul_neutral(int128 x) public {
     // Test for neutral elements
     assert(mul(x, one) == x);
     assert(mul(x, zero) == zero);
   }

   function testMul_logic(int128 x, int128 y) public {
     int128 res = mul(x, y);

     // If any operands is zero, or we lose all precision in the operation, result is zero
     if((x == zero || y == zero) || add(log_2(x), log_2(y)) < fromInt(-64)) {
       assert(res == zero);
     }
     // Otherwise, if both operands have the same sign, result is positive
     else if((x > zero && y > zero) || (x < zero && y < zero)) {
       assert(res > zero);
     } 
     // Otherwise, they have different sign, result is negative
     else if((x < zero && y > zero) || (x > zero && y < zero)) {
       assert(res < zero);
     }
          
   }

   function testMulu_logic(int128 x, uint256 y) public {
     // mulu rounds down, this means that dividing and multiplying by a number
     // should always be less than the original number

     // y can't be zero, but let's test if it returns 0
     if(y == 0) {
       assert(mulu(x, y) == 0);
       y++;
     }

     int128 fraction = div(x, fromUInt(y));
     assert(mulu(fraction, y) < uint128(x));

     // If x < 1, result should be < y, and viceversa
     uint256 mulResult = mulu(x, y);
     if(x < one) {
       assert(mulResult < y);
     }
     else if(x > one) {
       assert(mulResult > y);
     }
     else {
       assert(mulResult == y);
     }
     
   }

   function testMulu_overflow(int128 x, uint256 y) public {
     // Test revert on negative x
     if (x < zero && y != 0) {
       try this.mulu(x, y) { assert(false); } catch {}
     }
   }

   function testMuli_logic(int128 x, int256 y) public {
     // muli rounds towards zero, this means that it should have the same behaviour
     // as mulu, but with both positive and negative x

     // for y == 0, or x == 0, result is zero
     if(y == 0 || x == 0) {
       assert(muli(x, y) == zero);
     }
     if(y == 0) y++;

     int128 fraction = div(x, fromInt(y));
     assert(abs256(muli(fraction, y)) < abs256(x));

     // If x < 1, result should be < y, and viceversa
     int256 absMuli = abs256(muli(x, y));
     if(abs(x) < one) {
       assert( absMuli < abs256(y));
     }
     else if(abs(x) > one) {
       assert( absMuli > abs256(y));
     }
     else {
       assert( absMuli == abs256(y));
     }
   }

   function testDiv_div_by_zero(int128 x) public {
     // Test revert if y == 0
     try this.div(x, zero) { assert(false); } catch {}
   }

   function testDiv_neutral(int128 x) public {
     // Test for neutral operations
     assert(div(x, one) == x);
     assert(div(x, x) == one);
     assert(div(zero, x) == zero);
   }

   function testDiv_inverse(int128 x, int128 y) public {
     int128 divResult = div(x, y);
     int128 mulResult = mul(divResult, y);
     int128 ldiv = sub(log_2(x), log_2(y));
     int128 lmul = add(log_2(divResult), log_2(y));
     int128 lerror = abs(lmul - ldiv);

     // The result should be between 2**64 and 2**-64
     // for the below assertion to hold
     require(lerror > fromInt(-64) && lerror < fromInt(64));

     // The error should be less than 2**lerror
     assert(abs(sub(x, mulResult)) <= exp_2(lerror) );
   }

   function testDiv_equivalence_to_mul(int128 x, int128 y) public {
     int128 divResult = div(x, y);
     int128 mulResult = mul(x, inv(y));
     int128 ldiv = log_2(divResult);
     int128 lmul = log_2(mulResult);
     int128 lerror = abs(lmul - ldiv);

     assert( abs(sub(div(x, y), mul(x, inv(y)))) < exp_2(lerror) );
   }

   function testDiv_commutative(int128 x, int128 y) public {
     int128 div1Result = div(x, y);
     int128 div2Result = inv(div(y, x));

     assert( abs(sub(div1Result, div2Result)) <= exp_2(log_2(x) - log_2(y)) );
   }

   function testDiv_logic(int128 x, int128 y) public {
     // If performing division by an |y| > 1, the result must be less than the dividend
     // otherwise, it should be greater than the dividend
     int128 divResult = abs(div(x, y));
     if(abs(y) > one) {
       assert(divResult < abs(x));
     }
     else if (abs(y) < one) {
       assert(divResult > abs(x));
     }
     else {
       assert(divResult == abs(x));
     }
   }
  
   function testDivu_div_by_zero(uint256 x) public {
     // Test revert if y == 0
     try this.divu(x, 0) { assert(false); } catch {}
   }

   function testDivu_neutral(uint256 x) public {
     // Test for neutral operations
     assert(divu(x, 1) == fromUInt(x));
     assert(divu(x, x) == one);
     assert(divu(0, x) == zero);
   }

   function testDivu_logic(uint256 x, uint256 y) public {
     // TODO: Find the correct condition to allow full range
     // By the time being, limit the operands to 128 bits for fuzzing

     //x = x % 2**127;
     //y = y % 2**127;

     int128 divResult = divu(x, y);
     
     if(y - x < 2**128 || x - y < 2**128) {
      if(y > x) {
        assert(divResult < one);
      }
      else if (y < x) {
        assert(divResult > one);
      }
      else {
        assert(divResult == one);
      }
     }
   }


   function testNeg_neutral(int128 x) public {
     // Test for neutral operations
     assert(add(x, neg(x)) == zero);
     if(x > zero) {
       assert(sub(zero, x) == neg(x));
     }
   }

   function testAbs_neutral(int128 x) public {
     // Test for neutral operations
     if(x < zero) {
       assert(abs(x) == neg(x));
     }
     else {
       assert(abs(x) == x);
     }

   }

   function testAvg_logic(int128 x, int128 y) public {
     // Result should be in between both arguments
     int128 min; 
     int128 max;
     (min,max) = minmax(x, y);
     int128 average = avg(x, y);

     assert(average >= min && average <= max);

     // Average of equal values should be the same value
     assert(avg(x, x) == x);

     // Average of value and zero should be value/2 or slightly
     // less due to floor rounding
     assert(avg(x, 0) <= x/2);

   }

   function testGavg_logic(int128 x, int128 y) public {
     // Result should be in between both arguments
     int128 min; 
     int128 max;
     (min,max) = minmax(x, y);
     int128 average = gavg(x, y);

      if(x > zero)
        assert(average >= min && average <= max);
      else 
        assert(neg(average) >= min && neg(average) <= max);

     // Average of equal values should be the same value
     if(x >= zero) {
       assert(gavg(x, x) == x);
     } else {
       assert(gavg(x, x) == neg(x));
     }

     // Average of value and zero should be zero
     assert(gavg(x, zero) == zero);

   }

   function testPow_logic(int128 x, uint256 y) public {
     // 0 to the 0 should be 1
     assert(pow(zero, 0) == one);

     // If the base is less than one, the result should be less than one too
     // Otherwise, it should be greater than one
     if(abs(x) < one && x != 0 && y != 0) {
       assert(pow(x, y) < one );
     }
     if(abs(x) >= one) {
       assert(pow(x, y) >= one );
     }
     
   }

   function testSqrt_logic(int128 x) public {
     
     // As the function rounds down, x^2 should be higher than
     // sqrt(x)
     int128 sq = sqrt(x);
     assert(mul(sq, sq) <= x);
     
   }

   function testSqrt_revert(int128 x) public {
     // Negative arguments should revert
     if(x < 0) {
       try this.sqrt(x) { assert(false); } catch {}
     }
     
   }

   function testLog2_inverse(int128 x) public {
     // Check for inverse function
     int128 log2x = log_2(x);
     uint256 log2x_low = toUInt(log2x);
     uint256 log2x_high = log2x_low + 1;

     assert(x > exp_2(fromUInt(log2x_low)) && x < exp_2(fromUInt(log2x_high)));
     
   }

   function testLog2_revert(int128 x) public {
     // Negative  or zero arguments should revert
     if(x <= 0) {
       try this.log_2(x) { assert(false); } catch {}
     }
     
   }

   function testExp2_inverse(int128 x) public {
     // Check for inverse function
     /*int128 exp2x = exp_2(x);
     uint256 log2x_low = toUInt(exp2x);
     uint256 log2x_high = log2x_low + 1;

     assert(x > exp_2(fromUInt(log2x_low)) && x < exp_2(fromUInt(log2x_high)));*/
     emit Value("exp2x", exp_2(x));
     emit Value("log2x", log_2(exp_2(x)));
     assert(abs(sub(log_2(exp_2(x)), x)) < exp_2(fromInt(-60)));
   }

   function testExp2_revert(int128 x) public {
     // Reverts on overflow
     if(x >= 0x400000000000000000) {
       try this.exp(x) { assert(false); } catch {}
     }
   }

   function testLn_revert(int128 x) public {
     // For ln we test only reverts, as it's implemented 
     // based on log_2
     if(x <= 0) {
       try this.ln(x) { assert(false); } catch {}
     }
     
   }

   function testExp_revert(int128 x) public {
     // For exp we test only reverts, as it's implemented 
     // based on exp_2
     if(x >= 0x400000000000000000) {
       try this.exp(x) { assert(false); } catch {}
     }
     
   }

}
