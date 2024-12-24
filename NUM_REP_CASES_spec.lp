require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem71257 : Prf (∀ (λ a : El ind, (= (NUM_REP a) (∨ (= a IND_0) (∃ (λ i : El ind, (∧ (= a (IND_SUC i)) (NUM_REP i))))))));
