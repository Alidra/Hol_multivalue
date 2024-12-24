require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem80749 : Prf ((λ *' : El (fun num (fun num (fun num num))), (∀ (λ _2186 : El num, (∧ (∀ (λ n : El num, (= (*' _2186 (NUMERAL _0) n) (NUMERAL _0)))) (∀ (λ m : El num, (∀ (λ n : El num, (= (*' _2186 (SUC m) n) (+ (*' _2186 m n) n)))))))))) ((@ε (fun num (fun num (fun num num)))) (λ *' : El (fun num (fun num (fun num num))), (∀ (λ _2186 : El num, (∧ (∀ (λ n : El num, (= (*' _2186 (NUMERAL _0) n) (NUMERAL _0)))) (∀ (λ m : El num, (∀ (λ n : El num, (= (*' _2186 (SUC m) n) (+ (*' _2186 m n) n))))))))))));
