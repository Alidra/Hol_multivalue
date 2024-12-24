require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5243851 : Prf (∀ (λ s : El (fun real bool), (∀ (λ a : El real, (⇒ (∧ (¬ (= s (@EMPTY real))) (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le (real_abs x) a))))) (real_le (real_abs (inf s)) a))))));
