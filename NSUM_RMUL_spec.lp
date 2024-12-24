require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6932170 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ c : El num, (∀ (λ s : El (fun A bool), (= ((@nsum A) s (λ x : El A, (* (f x) c))) (* ((@nsum A) s f) c))))))));
