require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem77187 : Prf (= + ((@ε (fun num (fun num (fun num num)))) (λ +' : El (fun num (fun num (fun num num))), (∀ (λ _2155 : El num, (∧ (∀ (λ n : El num, (= (+' _2155 (NUMERAL _0) n) n))) (∀ (λ m : El num, (∀ (λ n : El num, (= (+' _2155 (SUC m) n) (SUC (+' _2155 m n))))))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))));
