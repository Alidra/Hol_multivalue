require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1101527 [_25328] : Prf (= (@EX _25328) ((@ε (fun (prod num num) (fun (fun _25328 bool) (fun (list _25328) bool)))) (λ EX' : El (fun (prod num num) (fun (fun _25328 bool) (fun (list _25328) bool))), (∀ (λ _17980 : El (prod num num), (∧ (∀ (λ P : El (fun _25328 bool), (= (EX' _17980 P (@NIL _25328)) F))) (∀ (λ h : El _25328, (∀ (λ P : El (fun _25328 bool), (∀ (λ t : El (list _25328), (= (EX' _17980 P ((@CONS _25328) h t)) (∨ (P h) (EX' _17980 P t))))))))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))))));
