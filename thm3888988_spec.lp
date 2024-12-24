require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3888988 [_100554] (b : El _100554) (a : El _100554) (cs : El (fun _100554 bool)) (P : El bool) : Prf (∧ (= (∧ (¬ ((@IN _100554) a (@EMPTY _100554))) P) P) (∧ (= (∧ (¬ ((@IN _100554) a ((@INSERT _100554) b (@EMPTY _100554)))) P) (∧ (¬ (= a b)) P)) (= (∧ (¬ ((@IN _100554) a ((@INSERT _100554) b cs))) P) (∧ (¬ (= a b)) (∧ (¬ ((@IN _100554) a cs)) P)))));
