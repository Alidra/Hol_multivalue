require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1098310 [A] : Prf (= (@LAST A) ((@ε (fun (prod num (prod num (prod num num))) (fun (list A) A))) (λ LAST' : El (fun (prod num (prod num (prod num num))) (fun (list A) A)), (∀ (λ _17954 : El (prod num (prod num (prod num num))), (∀ (λ h : El A, (∀ (λ t : El (list A), (= (LAST' _17954 ((@CONS A) h t)) ((@COND A) (= t (@NIL A)) h (LAST' _17954 t)))))))))) ((@̦‚ num (prod num (prod num num))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))));
