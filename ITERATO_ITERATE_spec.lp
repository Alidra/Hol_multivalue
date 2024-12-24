require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6889194 [A K] : Prf (∀ (λ op : El (fun A (fun A A)), (∀ (λ <<= : El (fun K (fun K bool)), (⇒ ((@monoidal A) op) (= ((@iterato A K) (@UNIV A) ((@neutral A) op) op <<=) ((@iterate A K) op)))))));
