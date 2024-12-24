require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8 : Prf (= ∧ (λ p : El bool, (λ q : El bool, (= (λ f : El (fun bool (fun bool bool)), (f p q)) (λ f : El (fun bool (fun bool bool)), (f T T))))));
