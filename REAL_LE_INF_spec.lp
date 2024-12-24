require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5238253 (s : El (fun real bool)) : Prf (∀ (λ b : El real, (⇒ (∧ (¬ (= s (@EMPTY real))) (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le b x))))) (real_le b (inf s)))));
