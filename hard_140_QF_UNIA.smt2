; (set-option :print-success true)
(set-option :produce-models true)
 ; dumped from SmtFormulaCheckerQuery rule_ctoken_rounding_match_user_needs
(set-logic QF_UFNIA)
(declare-fun B31 () Bool)
(declare-fun B34 () Bool)
(declare-fun B69 () Bool)
(declare-fun I11 () Int)
(declare-fun I13 () Int)
(declare-fun I22 () Int)
(declare-fun I43 () Int)
(declare-fun I46 () Int)
(declare-fun I49 () Int)
(declare-fun OK_0_0_0_0_0_0 () Bool)
(declare-fun R0 () Int)
(declare-fun R1 () Int)
(declare-fun R10 () Int)
(declare-fun R16 () Int)
(declare-fun R18 () Int)
(declare-fun R19 () Int)
(declare-fun R2 () Int)
(declare-fun R21 () Int)
(declare-fun R23 () Int)
(declare-fun R25 () Int)
(declare-fun R26 () Int)
(declare-fun R28 () Int)
(declare-fun R29 () Int)
(declare-fun R3 () Int)
(declare-fun R30 () Int)
(declare-fun R33 () Int)
(declare-fun R35 () Int)
(declare-fun R36 () Int)
(declare-fun R37 () Int)
(declare-fun R39 () Int)
(declare-fun R4 () Int)
(declare-fun R40 () Int)
(declare-fun R41 () Int)
(declare-fun R45 () Int)
(declare-fun R51 () Int)
(declare-fun R52 () Int)
(declare-fun R55 () Int)
(declare-fun R58 () Int)
(declare-fun R6 () Int)
(declare-fun R62 () Int)
(declare-fun R63 () Int)
(declare-fun R64 () Int)
(declare-fun R66 () Int)
(declare-fun R67 () Int)
(declare-fun R7 () Int)
(declare-fun R9 () Int)
(declare-fun ReachabilityCertora0_0_0_0_0_0 () Bool)
(declare-fun pi_base (Int) Int)
(declare-fun pi_isLargeConstant (Int) Bool)
(declare-fun uninterp_bwand (Int Int) Int)
(declare-fun uninterp_bwlshr (Int Int) Int)
(define-fun
  axiom_evm_bound_2to256
  ((a!a Int))
  Bool
  (and
    (>= a!a 0)
    (< a!a 115792089237316195423570985008687907853269984665640564039457584007913129639936)
  )
)
(define-fun
  axiom_bwand_fullmask
  ((a!a Int))
  Bool
  (and
    (=
      (uninterp_bwand a!a 115792089237316195423570985008687907853269984665640564039457584007913129639935)
      a!a
    )
    (=
      (uninterp_bwand 115792089237316195423570985008687907853269984665640564039457584007913129639935 a!a)
      a!a
    )
  )
)
(define-fun
  axiom_bwand_withzero
  ((a!a Int))
  Bool
  (and
    (=
      (uninterp_bwand a!a 0)
      0
    )
    (=
      (uninterp_bwand 0 a!a)
      0
    )
  )
)
(define-fun
  axiom_bwand_eq
  ((a!a Int))
  Bool
  (=
    (uninterp_bwand a!a a!a)
    a!a
  )
)
(define-fun
  axiom_combinedBwandArg
  ((a!a Int))
  Bool
  (and
    (axiom_bwand_fullmask a!a)
    (axiom_bwand_withzero a!a)
    (axiom_bwand_eq a!a)
  )
)
(define-fun
  axiom_bwand_commute
  ((a!a Int) (b!b Int))
  Bool
  (=
    (uninterp_bwand a!a b!b)
    (uninterp_bwand b!b a!a)
  )
)
(define-fun
  axiom_bwand_bound
  ((a!a Int) (b!b Int))
  Bool
  (and
    (=>
      (>= a!a 0)
      (<=
        (uninterp_bwand a!a b!b)
        a!a
      )
    )
    (=>
      (>= b!b 0)
      (<=
        (uninterp_bwand a!a b!b)
        b!b
      )
    )
    (>=
      (uninterp_bwand a!a b!b)
      0
    )
  )
)
(define-fun
  axiom_combinedBwandApp
  ((a!a Int) (b!b Int))
  Bool
  (and
    (axiom_bwand_commute a!a b!b)
    (axiom_bwand_bound a!a b!b)
  )
)
(define-fun
  axiom_bwand_3fffffffc000_via_mod
  ((a!a Int))
  Bool
  (=
    (uninterp_bwand a!a 70368744161280)
    (-
      (mod a!a 70368744177664)
      (mod a!a 16384)
    )
  )
)
(define-fun
  axiom_combinedBwand_3fffffffc000
  ((a!a Int))
  Bool
  (and
    (axiom_bwand_3fffffffc000_via_mod a!a)
    (axiom_combinedBwandApp a!a 70368744161280)
  )
)
(define-fun
  axiom_bwand_ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000_via_mod
  ((a!a Int))
  Bool
  (=
    (uninterp_bwand a!a 115792089237316195423570985008687907853269984665640564039457584007913129623552)
    (-
      a!a
      (mod a!a 16384)
    )
  )
)
(define-fun
  axiom_combinedBwand_ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000
  ((a!a Int))
  Bool
  (and
    (axiom_bwand_ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000_via_mod a!a)
    (axiom_combinedBwandApp a!a 115792089237316195423570985008687907853269984665640564039457584007913129623552)
  )
)
(define-fun
  axiom_bwand_ffffffffffffffff_via_mod
  ((a!a Int))
  Bool
  (=
    (uninterp_bwand a!a 18446744073709551615)
    (mod a!a 18446744073709551616)
  )
)
(define-fun
  axiom_combinedBwand_ffffffffffffffff
  ((a!a Int))
  Bool
  (and
    (axiom_bwand_ffffffffffffffff_via_mod a!a)
    (axiom_combinedBwandApp a!a 18446744073709551615)
  )
)
(define-fun
  axiom_bwand_3fff_via_mod
  ((a!a Int))
  Bool
  (=
    (uninterp_bwand a!a 16383)
    (mod a!a 16384)
  )
)
(define-fun
  axiom_combinedBwand_3fff
  ((a!a Int))
  Bool
  (and
    (axiom_bwand_3fff_via_mod a!a)
    (axiom_combinedBwandApp a!a 16383)
  )
)
(assert
  (=
    OK_0_0_0_0_0_0
    (=>
      (and
        (= R0 8589942784)
        (>= R1 1)
        (<= R1 18446744073709551615)
        (>= R2 1)
        (<= R2 4294967295)
        (=
          R3
          (* 16384 R2)
        )
        (=
          R4
          (uninterp_bwand 70368744161280 R3)
        )
        (<= R4 R1)
        (= R6 14)
        (>= R7 1)
        (<= R7 18446744073709551615)
        (<= R7 R1)
        (= R9 8589942672)
        (=
          R10
          (uninterp_bwand 115792089237316195423570985008687907853269984665640564039457584007913129623552 R7)
        )
        (=
          I11
          (* R10 R2)
        )
        (>= I11 0)
        (<= I11 18446744073709551615)
        (=
          I13
          (+ R1 I11)
        )
        (>= I13 1)
        (<= I13 18446744073709551616)
        (=
          R16
          (- I13 1)
        )
        (= R18 1)
        (=
          R19
          (uninterp_bwand
            18446744073709551615
            (* 16384 R16)
          )
        )
        (=
          R21
          (+
            (*
              18446744073709551616
              (uninterp_bwlshr R16 50)
            )
            R19
          )
        )
        (=
          I22
          (ite
            (= R1 0)
            0
            (div R21 R1)
          )
        )
        (>= I22 0)
        (<= I22 18446744073709551615)
        (= R23 I22)
        (= R25 8589942696)
        (=
          R26
          (uninterp_bwand 115792089237316195423570985008687907853269984665640564039457584007913129623552 R23)
        )
        (=
          R28
          (+ 16384 R26)
        )
        (=
          R29
          (uninterp_bwand 18446744073709551615 R28)
        )
        (=
          R30
          (uninterp_bwand 16383 R23)
        )
        (=
          B31
          (= R30 0)
        )
        (or
          B31
          (<= R28 18446744073709551615)
        )
        (=
          R33
          (ite
            (= R30 0)
            R26
            R29
          )
        )
        (=
          B34
          (= R33 0)
        )
        (=
          R35
          (uninterp_bwlshr R33 14)
        )
        (=
          R36
          (ite B34 0 R35)
        )
        (=
          R37
          (ite B34 0 R35)
        )
        (=
          R39
          (* 16384 R36)
        )
        (=
          R40
          (ite
            (= R36 0)
            0
            R39
          )
        )
        (= R41 8589942672)
        (=
          I43
          (*
            (uninterp_bwlshr R1 14)
            R40
          )
        )
        (>= I43 0)
        (<= I43 18446744073709551615)
        (=
          R45
          (uninterp_bwand
            18446744073709551615
            (* 1125899906842624 R1)
          )
        )
        (=
          I46
          (* R40 R45)
        )
        (=
          I49
          (+
            I43
            (uninterp_bwlshr I46 64)
          )
        )
        (>= I49 0)
        (<= I49 18446744073709551615)
        (=
          R51
          (ite
            (= R2 0)
            0
            (div I49 R2)
          )
        )
        (=
          R52
          (uninterp_bwand 115792089237316195423570985008687907853269984665640564039457584007913129623552 R51)
        )
        (=
          R55
          (ite
            (= R52 0)
            0
            (uninterp_bwlshr R51 14)
          )
        )
        (=
          R58
          (ite
            (= R10 0)
            0
            (uninterp_bwlshr R7 14)
          )
        )
        (= R62 14)
        (= R63 14)
        (= R64 14)
        (=
          R66
          (* 16384 R37)
        )
        (=
          R67
          (ite
            (= R37 0)
            0
            R66
          )
        )
        (<= R67 R51)
        (=
          B69
          (<= R7 R51)
        )
      )
      B69
    )
  )
)
(assert
  (not OK_0_0_0_0_0_0)
)
(assert
  (= ReachabilityCertora0_0_0_0_0_0 true)
)
(assert
  (=
    (pi_base 8589942784)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 18446744073709551615)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 4294967295)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 16384)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 70368744161280)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 8589942672)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 115792089237316195423570985008687907853269984665640564039457584007913129623552)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 18446744073709551616)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 8589942696)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 16383)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (=
    (pi_base 1125899906842624)
    0
  )
) ; base(<largeConstantInCode>) == 0
(assert
  (pi_isLargeConstant 8589942784)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 18446744073709551615)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 4294967295)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 16384)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 70368744161280)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 8589942672)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 115792089237316195423570985008687907853269984665640564039457584007913129623552)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 18446744073709551616)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 8589942696)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 16383)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (pi_isLargeConstant 1125899906842624)
) ; isLargeConstant(<largeConstantInCode>)
(assert
  (axiom_combinedBwandArg R3)
)
(assert
  (axiom_combinedBwandArg 70368744161280)
)
(assert
  (axiom_combinedBwandArg R7)
)
(assert
  (axiom_combinedBwandArg 115792089237316195423570985008687907853269984665640564039457584007913129623552)
)
(assert
  (axiom_combinedBwandArg
    (* 16384 R16)
  )
)
(assert
  (axiom_combinedBwandArg 18446744073709551615)
)
(assert
  (axiom_combinedBwandArg R23)
)
(assert
  (axiom_combinedBwandArg R28)
)
(assert
  (axiom_combinedBwandArg 16383)
)
(assert
  (axiom_combinedBwandArg
    (* 1125899906842624 R1)
  )
)
(assert
  (axiom_combinedBwandArg R51)
)
(assert
  (axiom_combinedBwand_3fffffffc000 R3)
)
(assert
  (axiom_combinedBwand_ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000 R7)
)
(assert
  (axiom_combinedBwand_ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000 R23)
)
(assert
  (axiom_combinedBwand_ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000 R51)
)
(assert
  (axiom_combinedBwand_ffffffffffffffff
    (* 16384 R16)
  )
)
(assert
  (axiom_combinedBwand_ffffffffffffffff R28)
)
(assert
  (axiom_combinedBwand_ffffffffffffffff
    (* 1125899906842624 R1)
  )
)
(assert
  (axiom_combinedBwand_3fff R23)
)
(assert
  (=
    (uninterp_bwlshr R16 50)
    (div R16 1125899906842624)
  )
) ; shift right logical same as div
(assert
  (=
    (uninterp_bwlshr R33 14)
    (div R33 16384)
  )
) ; shift right logical same as div
(assert
  (=
    (uninterp_bwlshr R1 14)
    (div R1 16384)
  )
) ; shift right logical same as div
(assert
  (=
    (uninterp_bwlshr I46 64)
    (div I46 18446744073709551616)
  )
) ; shift right logical same as div
(assert
  (=
    (uninterp_bwlshr R51 14)
    (div R51 16384)
  )
) ; shift right logical same as div
(assert
  (=
    (uninterp_bwlshr R7 14)
    (div R7 16384)
  )
) ; shift right logical same as div
(assert
  (axiom_evm_bound_2to256 R0)
) ; 
(assert
  (axiom_evm_bound_2to256 R1)
) ; 
(assert
  (axiom_evm_bound_2to256 R2)
) ; 
(assert
  (axiom_evm_bound_2to256 R3)
) ; 
(assert
  (axiom_evm_bound_2to256 R4)
) ; 
(assert
  (axiom_evm_bound_2to256 R6)
) ; 
(assert
  (axiom_evm_bound_2to256 R7)
) ; 
(assert
  (axiom_evm_bound_2to256 R9)
) ; 
(assert
  (axiom_evm_bound_2to256 R10)
) ; 
(assert
  (axiom_evm_bound_2to256 R16)
) ; 
(assert
  (axiom_evm_bound_2to256 R18)
) ; 
(assert
  (axiom_evm_bound_2to256 R19)
) ; 
(assert
  (axiom_evm_bound_2to256 R21)
) ; 
(assert
  (axiom_evm_bound_2to256 R23)
) ; 
(assert
  (axiom_evm_bound_2to256 R25)
) ; 
(assert
  (axiom_evm_bound_2to256 R26)
) ; 
(assert
  (axiom_evm_bound_2to256 R28)
) ; 
(assert
  (axiom_evm_bound_2to256 R29)
) ; 
(assert
  (axiom_evm_bound_2to256 R30)
) ; 
(assert
  (axiom_evm_bound_2to256 R33)
) ; 
(assert
  (axiom_evm_bound_2to256 R35)
) ; 
(assert
  (axiom_evm_bound_2to256 R36)
) ; 
(assert
  (axiom_evm_bound_2to256 R37)
) ; 
(assert
  (axiom_evm_bound_2to256 R39)
) ; 
(assert
  (axiom_evm_bound_2to256 R40)
) ; 
(assert
  (axiom_evm_bound_2to256 R41)
) ; 
(assert
  (axiom_evm_bound_2to256 R45)
) ; 
(assert
  (axiom_evm_bound_2to256 R51)
) ; 
(assert
  (axiom_evm_bound_2to256 R52)
) ; 
(assert
  (axiom_evm_bound_2to256 R55)
) ; 
(assert
  (axiom_evm_bound_2to256 R58)
) ; 
(assert
  (axiom_evm_bound_2to256 R62)
) ; 
(assert
  (axiom_evm_bound_2to256 R63)
) ; 
(assert
  (axiom_evm_bound_2to256 R64)
) ; 
(assert
  (axiom_evm_bound_2to256 R66)
) ; 
(assert
  (axiom_evm_bound_2to256 R67)
) ;
(get-info :reason-unknown)
