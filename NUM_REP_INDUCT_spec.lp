require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem71258 : Prf (∀ (λ NUM_REP' : El (fun ind bool), (⇒ (∧ (NUM_REP' IND_0) (∀ (λ i : El ind, (⇒ (NUM_REP' i) (NUM_REP' (IND_SUC i)))))) (∀ (λ a : El ind, (⇒ (NUM_REP a) (NUM_REP' a)))))));
