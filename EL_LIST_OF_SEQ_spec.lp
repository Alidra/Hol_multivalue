require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1237532 [A] : Prf (∀ (λ s : El (fun num A), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (< m n) (= ((@EL A) m ((@list_of_seq A) s n)) (s m)))))))));
