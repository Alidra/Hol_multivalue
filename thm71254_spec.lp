require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem71254 : Prf (∧ (∧ (NUM_REP IND_0) (∀ (λ i : El ind, (⇒ (NUM_REP i) (NUM_REP (IND_SUC i)))))) (∧ (∀ (λ NUM_REP' : El (fun ind bool), (⇒ (∧ (NUM_REP' IND_0) (∀ (λ i : El ind, (⇒ (NUM_REP' i) (NUM_REP' (IND_SUC i)))))) (∀ (λ a : El ind, (⇒ (NUM_REP a) (NUM_REP' a))))))) (∀ (λ a : El ind, (= (NUM_REP a) (∨ (= a IND_0) (∃ (λ i : El ind, (∧ (= a (IND_SUC i)) (NUM_REP i))))))))));
