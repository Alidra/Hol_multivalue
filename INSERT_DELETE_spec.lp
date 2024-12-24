require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3319650 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ ((@IN A) x s) (= ((@INSERT A) x ((@DELETE A) s x)) s))))));
