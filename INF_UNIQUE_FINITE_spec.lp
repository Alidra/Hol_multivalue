require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5252869 (a : El real) : Prf (∀ (λ s : El (fun real bool), (⇒ (∧ ((@FINITE real) s) (¬ (= s (@EMPTY real)))) (= (= (inf s) a) (∧ ((@IN real) a s) (∀ (λ y : El real, (⇒ ((@IN real) y s) (real_le a y)))))))));
