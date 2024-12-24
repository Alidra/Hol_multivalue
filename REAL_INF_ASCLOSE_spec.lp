require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5248524 : Prf (∀ (λ s : El (fun real bool), (∀ (λ l : El real, (∀ (λ e : El real, (⇒ (∧ (¬ (= s (@EMPTY real))) (∀ (λ x : El real, (⇒ ((@IN real) x s) (real_le (real_abs (real_sub x l)) e))))) (real_le (real_abs (real_sub (inf s) l)) e))))))));
