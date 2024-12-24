require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5436088 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@FINITE A) s) (∃ (λ k : El (fun num bool), (∃ (λ f : El (fun num A), (∧ (∀ (λ i : El num, (∀ (λ j : El num, (⇒ (∧ ((@IN num) i k) (∧ ((@IN num) j k) (= (f i) (f j)))) (= i j)))))) (∧ ((@FINITE num) k) (= s ((@IMAGE num A) f k)))))))))));
