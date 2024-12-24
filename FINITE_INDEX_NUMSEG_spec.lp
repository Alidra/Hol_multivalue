require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5423178 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@FINITE A) s) (∃ (λ f : El (fun num A), (∧ (∀ (λ i : El num, (∀ (λ j : El num, (⇒ (∧ ((@IN num) i (… (NUMERAL (BIT1 _0)) ((@CARD A) s))) (∧ ((@IN num) j (… (NUMERAL (BIT1 _0)) ((@CARD A) s))) (= (f i) (f j)))) (= i j)))))) (= s ((@IMAGE num A) f (… (NUMERAL (BIT1 _0)) ((@CARD A) s))))))))));
