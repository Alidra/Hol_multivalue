require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1105686 [_25569] : Prf (= (@EL _25569) ((@ε (fun (prod num num) (fun num (fun (list _25569) _25569)))) (λ EL' : El (fun (prod num num) (fun num (fun (list _25569) _25569))), (∀ (λ _18015 : El (prod num num), (∧ (∀ (λ l : El (list _25569), (= (EL' _18015 (NUMERAL _0) l) ((@HD _25569) l)))) (∀ (λ n : El num, (∀ (λ l : El (list _25569), (= (EL' _18015 (SUC n) l) (EL' _18015 n ((@TL _25569) l))))))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))));
