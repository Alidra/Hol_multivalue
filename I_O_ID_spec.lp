require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem15708 [A B] : Prf (∀ (λ f : El (fun A B), (∧ (= ((@o A B B) (@I B) f) f) (= ((@o A A B) f (@I A)) f))));
