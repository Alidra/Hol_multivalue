require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FORALL_UNION_OF_term_abbrevs;
require open hol-light.thm4845732_spec;
require open hol-light.thm4848608_spec;
opaque symbol lem4848609 [_111301] (P : El (type180 _111301)) (Q : El (type686 _111301)) (R : El (type686 _111301)) : Prf (= (term0 _111301 P Q R) (term1 _111301 P Q R)) ≔ EQ_MP (@lem4845732 _111301 P Q R) (@lem4848608 _111301 P Q R);
