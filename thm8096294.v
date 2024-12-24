Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8096294_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Lemma lem8096088 {_4656 _4660 : Type'} : (@_MATCH _4656 _4660) = (term0 _4656 _4660).
Proof. exact (@_MATCH_def _4656 _4660). Qed.
Lemma lem8096089 {_143642 _143649 : Type'} : (@_MATCH _143649 _143642) = (term1 _143642 _143649).
Proof. exact (@lem8096088 _143649 _143642). Qed.
Lemma lem8096090 {_143649 : Type'} (x : _143649) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8096091 {_143642 _143649 : Type'} (x : _143649) : (@_MATCH _143649 _143642 x) = (term2 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096089 _143642 _143649) (@lem8096090 _143649 x)). Qed.
Lemma lem8096093 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096094 {_143642 _143649 : Type'} (f : type1450 _143642 _143649) (y : _143649) : (term4 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096093 _143649 (type743 _143642 _143649) f y). Qed.
Lemma lem8096095 {_143642 _143649 : Type'} (x : _143649) : (term5 _143642 _143649 x) = (term2 _143642 _143649 x).
Proof. exact (@lem8096094 _143642 _143649 (term1 _143642 _143649) x). Qed.
Lemma lem8096096 {_143642 _143649 : Type'} (e : _143649) : (term2 _143642 _143649 e) = (term6 _143642 _143649 e).
Proof. exact (eq_refl (term2 _143642 _143649 e)). Qed.
Lemma lem8096097 {_143642 _143649 : Type'} : (term7 _143642 _143649) = (term1 _143642 _143649).
Proof. exact (fun_ext (fun e : _143649 => @lem8096096 _143642 _143649 e)). Qed.
Lemma lem8096098 {_143649 : Type'} (x : _143649) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8096099 {_143642 _143649 : Type'} (x : _143649) : (term5 _143642 _143649 x) = (term2 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096097 _143642 _143649) (@lem8096098 _143649 x)). Qed.
Lemma lem8096100 {_143642 _143649 : Type'} : (@eq ((_143649 -> _143642 -> Prop) -> _143642)) = (@eq ((_143649 -> _143642 -> Prop) -> _143642)).
Proof. exact (eq_refl (@eq ((_143649 -> _143642 -> Prop) -> _143642))). Qed.
Lemma lem8096101 {_143642 _143649 : Type'} (x : _143649) : (term8 _143642 _143649 x) = (term9 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096100 _143642 _143649) (@lem8096099 _143642 _143649 x)). Qed.
Lemma lem8096102 {_143642 _143649 : Type'} (x : _143649) : (term2 _143642 _143649 x) = (term6 _143642 _143649 x).
Proof. exact (eq_refl (term2 _143642 _143649 x)). Qed.
Lemma lem8096103 {_143642 _143649 : Type'} (x : _143649) : ((term5 _143642 _143649 x) = (term2 _143642 _143649 x)) = ((term2 _143642 _143649 x) = (term6 _143642 _143649 x)).
Proof. exact (MK_COMB (@lem8096101 _143642 _143649 x) (@lem8096102 _143642 _143649 x)). Qed.
Lemma lem8096104 {_143642 _143649 : Type'} (x : _143649) : (term2 _143642 _143649 x) = (term6 _143642 _143649 x).
Proof. exact (EQ_MP (@lem8096103 _143642 _143649 x) (@lem8096095 _143642 _143649 x)). Qed.
Lemma lem8096105 {_143642 _143649 : Type'} (x : _143649) : (@_MATCH _143649 _143642 x) = (term6 _143642 _143649 x).
Proof. exact (TRANS (@lem8096091 _143642 _143649 x) (@lem8096104 _143642 _143649 x)). Qed.
Lemma lem8096107 {_4611 _4614 : Type'} : (@_SEQPATTERN _4611 _4614) = (term10 _4611 _4614).
Proof. exact (@_SEQPATTERN_def _4611 _4614). Qed.
Lemma lem8096108 {_143642 _143649 : Type'} : (@_SEQPATTERN _143642 _143649) = (term10 _143642 _143649).
Proof. exact (@lem8096107 _143642 _143649). Qed.
Lemma lem8096113 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem8096114 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : (@_SEQPATTERN _143642 _143649 r) = (term11 _143642 _143649 r).
Proof. exact (MK_COMB (@lem8096108 _143642 _143649) (@lem8096113 _143642 _143649 r)). Qed.
Lemma lem8096116 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096117 {_143642 _143649 : Type'} (f : type731 _143642 _143649) (y : type1470 _143642 _143649) : (term12 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096116 (type1470 _143642 _143649) (type741 _143642 _143649) f y). Qed.
Lemma lem8096118 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : (term13 _143642 _143649 r) = (term11 _143642 _143649 r).
Proof. exact (@lem8096117 _143642 _143649 (term10 _143642 _143649) r). Qed.
Lemma lem8096119 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : (term11 _143642 _143649 r) = (term14 _143642 _143649 r).
Proof. exact (eq_refl (term11 _143642 _143649 r)). Qed.
Lemma lem8096120 {_143642 _143649 : Type'} : (term15 _143642 _143649) = (term10 _143642 _143649).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8096119 _143642 _143649 r)). Qed.
Lemma lem8096121 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem8096122 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : (term13 _143642 _143649 r) = (term11 _143642 _143649 r).
Proof. exact (MK_COMB (@lem8096120 _143642 _143649) (@lem8096121 _143642 _143649 r)). Qed.
Lemma lem8096123 {_143642 _143649 : Type'} : (@eq ((_143649 -> _143642 -> Prop) -> _143649 -> _143642 -> Prop)) = (@eq ((_143649 -> _143642 -> Prop) -> _143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@eq ((_143649 -> _143642 -> Prop) -> _143649 -> _143642 -> Prop))). Qed.
Lemma lem8096124 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : (term16 _143642 _143649 r) = (term17 _143642 _143649 r).
Proof. exact (MK_COMB (@lem8096123 _143642 _143649) (@lem8096122 _143642 _143649 r)). Qed.
Lemma lem8096125 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : (term11 _143642 _143649 r) = (term14 _143642 _143649 r).
Proof. exact (eq_refl (term11 _143642 _143649 r)). Qed.
Lemma lem8096126 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : ((term13 _143642 _143649 r) = (term11 _143642 _143649 r)) = ((term11 _143642 _143649 r) = (term14 _143642 _143649 r)).
Proof. exact (MK_COMB (@lem8096124 _143642 _143649 r) (@lem8096125 _143642 _143649 r)). Qed.
Lemma lem8096127 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : (term11 _143642 _143649 r) = (term14 _143642 _143649 r).
Proof. exact (EQ_MP (@lem8096126 _143642 _143649 r) (@lem8096118 _143642 _143649 r)). Qed.
Lemma lem8096132 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : (@_SEQPATTERN _143642 _143649 r) = (term14 _143642 _143649 r).
Proof. exact (TRANS (@lem8096114 _143642 _143649 r) (@lem8096127 _143642 _143649 r)). Qed.
Lemma lem8096133 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem8096134 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (@_SEQPATTERN _143642 _143649 r s) = (term18 _143642 _143649 r s).
Proof. exact (MK_COMB (@lem8096132 _143642 _143649 r) (@lem8096133 _143642 _143649 s)). Qed.
Lemma lem8096136 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096137 {_143642 _143649 : Type'} (f : type741 _143642 _143649) (y : type1470 _143642 _143649) : (term19 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096136 (type1470 _143642 _143649) (type1470 _143642 _143649) f y). Qed.
Lemma lem8096138 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term20 _143642 _143649 r s) = (term18 _143642 _143649 r s).
Proof. exact (@lem8096137 _143642 _143649 (term14 _143642 _143649 r) s). Qed.
Lemma lem8096139 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term18 _143642 _143649 r s) = (term21 _143642 _143649 r s).
Proof. exact (eq_refl (term18 _143642 _143649 r s)). Qed.
Lemma lem8096140 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : (term22 _143642 _143649 r) = (term14 _143642 _143649 r).
Proof. exact (fun_ext (fun s : type1470 _143642 _143649 => @lem8096139 _143642 _143649 r s)). Qed.
Lemma lem8096141 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem8096142 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term20 _143642 _143649 r s) = (term18 _143642 _143649 r s).
Proof. exact (MK_COMB (@lem8096140 _143642 _143649 r) (@lem8096141 _143642 _143649 s)). Qed.
Lemma lem8096143 {_143642 _143649 : Type'} : (@eq (_143649 -> _143642 -> Prop)) = (@eq (_143649 -> _143642 -> Prop)).
Proof. exact (eq_refl (@eq (_143649 -> _143642 -> Prop))). Qed.
Lemma lem8096144 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term23 _143642 _143649 r s) = (term24 _143642 _143649 r s).
Proof. exact (MK_COMB (@lem8096143 _143642 _143649) (@lem8096142 _143642 _143649 r s)). Qed.
Lemma lem8096145 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term18 _143642 _143649 r s) = (term21 _143642 _143649 r s).
Proof. exact (eq_refl (term18 _143642 _143649 r s)). Qed.
Lemma lem8096146 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : ((term20 _143642 _143649 r s) = (term18 _143642 _143649 r s)) = ((term18 _143642 _143649 r s) = (term21 _143642 _143649 r s)).
Proof. exact (MK_COMB (@lem8096144 _143642 _143649 r s) (@lem8096145 _143642 _143649 r s)). Qed.
Lemma lem8096147 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term18 _143642 _143649 r s) = (term21 _143642 _143649 r s).
Proof. exact (EQ_MP (@lem8096146 _143642 _143649 r s) (@lem8096138 _143642 _143649 r s)). Qed.
Lemma lem8096152 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (@_SEQPATTERN _143642 _143649 r s) = (term21 _143642 _143649 r s).
Proof. exact (TRANS (@lem8096134 _143642 _143649 r s) (@lem8096147 _143642 _143649 r s)). Qed.
Lemma lem8096153 {_143642 _143649 : Type'} (x : _143649) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term25 _143642 _143649 x r s) = (term26 _143642 _143649 x r s).
Proof. exact (MK_COMB (@lem8096105 _143642 _143649 x) (@lem8096152 _143642 _143649 r s)). Qed.
Lemma lem8096155 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096156 {_143642 _143649 : Type'} (f : type743 _143642 _143649) (y : type1470 _143642 _143649) : (term27 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096155 (type1470 _143642 _143649) _143642 f y). Qed.
Lemma lem8096157 {_143642 _143649 : Type'} (x : _143649) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term28 _143642 _143649 x r s) = (term26 _143642 _143649 x r s).
Proof. exact (@lem8096156 _143642 _143649 (term6 _143642 _143649 x) (term21 _143642 _143649 r s)). Qed.
Lemma lem8096158 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term29 _143642 _143649 x r) = (term30 _143642 _143649 r x).
Proof. exact (eq_refl (term29 _143642 _143649 x r)). Qed.
Lemma lem8096159 {_143642 _143649 : Type'} (x : _143649) : (term31 _143642 _143649 x) = (term6 _143642 _143649 x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8096158 _143642 _143649 r x)). Qed.
Lemma lem8096160 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term21 _143642 _143649 r s) = (term21 _143642 _143649 r s).
Proof. exact (eq_refl (term21 _143642 _143649 r s)). Qed.
Lemma lem8096161 {_143642 _143649 : Type'} (x : _143649) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term28 _143642 _143649 x r s) = (term26 _143642 _143649 x r s).
Proof. exact (MK_COMB (@lem8096159 _143642 _143649 x) (@lem8096160 _143642 _143649 r s)). Qed.
Lemma lem8096162 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8096163 {_143642 _143649 : Type'} (x : _143649) (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term32 _143642 _143649 x r s) = (term33 _143642 _143649 x r s).
Proof. exact (MK_COMB (@lem8096162 _143642) (@lem8096161 _143642 _143649 x r s)). Qed.
Lemma lem8096164 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term26 _143642 _143649 x r s) = (term34 _143642 _143649 r s x).
Proof. exact (eq_refl (term26 _143642 _143649 x r s)). Qed.
Lemma lem8096165 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term28 _143642 _143649 x r s) = (term26 _143642 _143649 x r s)) = ((term26 _143642 _143649 x r s) = (term34 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8096163 _143642 _143649 x r s) (@lem8096164 _143642 _143649 r s x)). Qed.
Lemma lem8096166 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term26 _143642 _143649 x r s) = (term34 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8096165 _143642 _143649 r s x) (@lem8096157 _143642 _143649 x r s)). Qed.
Lemma lem8096168 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096169 {_143642 _143649 : Type'} (f : type1470 _143642 _143649) (y : _143649) : (term35 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096168 _143649 (_143642 -> Prop) f y). Qed.
Lemma lem8096170 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term36 _143642 _143649 r s x) = (term37 _143642 _143649 r s x).
Proof. exact (@lem8096169 _143642 _143649 (term21 _143642 _143649 r s) x). Qed.
Lemma lem8096171 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term37 _143642 _143649 r s x) = (term38 _143642 _143649 r s x).
Proof. exact (eq_refl (term37 _143642 _143649 r s x)). Qed.
Lemma lem8096172 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term39 _143642 _143649 r s) = (term21 _143642 _143649 r s).
Proof. exact (fun_ext (fun x : _143649 => @lem8096171 _143642 _143649 r s x)). Qed.
Lemma lem8096173 {_143649 : Type'} (x : _143649) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8096174 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term36 _143642 _143649 r s x) = (term37 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096172 _143642 _143649 r s) (@lem8096173 _143649 x)). Qed.
Lemma lem8096175 {_143642 : Type'} : (@eq (_143642 -> Prop)) = (@eq (_143642 -> Prop)).
Proof. exact (eq_refl (@eq (_143642 -> Prop))). Qed.
Lemma lem8096176 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term40 _143642 _143649 r s x) = (term41 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096175 _143642) (@lem8096174 _143642 _143649 r s x)). Qed.
Lemma lem8096177 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term37 _143642 _143649 r s x) = (term38 _143642 _143649 r s x).
Proof. exact (eq_refl (term37 _143642 _143649 r s x)). Qed.
Lemma lem8096178 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term36 _143642 _143649 r s x) = (term37 _143642 _143649 r s x)) = ((term37 _143642 _143649 r s x) = (term38 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8096176 _143642 _143649 r s x) (@lem8096177 _143642 _143649 r s x)). Qed.
Lemma lem8096179 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term37 _143642 _143649 r s x) = (term38 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8096178 _143642 _143649 r s x) (@lem8096170 _143642 _143649 r s x)). Qed.
Lemma lem8096184 {_143642 : Type'} : (@ex1 _143642) = (@ex1 _143642).
Proof. exact (eq_refl (@ex1 _143642)). Qed.
Lemma lem8096185 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term42 _143642 _143649 r s x) = (term43 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096184 _143642) (@lem8096179 _143642 _143649 r s x)). Qed.
Lemma lem8096186 {_143642 : Type'} : (@COND _143642) = (@COND _143642).
Proof. exact (eq_refl (@COND _143642)). Qed.
Lemma lem8096187 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term44 _143642 _143649 r s x) = (term45 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096186 _143642) (@lem8096185 _143642 _143649 r s x)). Qed.
Lemma lem8096189 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096190 {_143642 _143649 : Type'} (f : type1470 _143642 _143649) (y : _143649) : (term35 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096189 _143649 (_143642 -> Prop) f y). Qed.
Lemma lem8096191 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term36 _143642 _143649 r s x) = (term37 _143642 _143649 r s x).
Proof. exact (@lem8096190 _143642 _143649 (term21 _143642 _143649 r s) x). Qed.
Lemma lem8096192 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term37 _143642 _143649 r s x) = (term38 _143642 _143649 r s x).
Proof. exact (eq_refl (term37 _143642 _143649 r s x)). Qed.
Lemma lem8096193 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) : (term39 _143642 _143649 r s) = (term21 _143642 _143649 r s).
Proof. exact (fun_ext (fun x : _143649 => @lem8096192 _143642 _143649 r s x)). Qed.
Lemma lem8096194 {_143649 : Type'} (x : _143649) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8096195 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term36 _143642 _143649 r s x) = (term37 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096193 _143642 _143649 r s) (@lem8096194 _143649 x)). Qed.
Lemma lem8096196 {_143642 : Type'} : (@eq (_143642 -> Prop)) = (@eq (_143642 -> Prop)).
Proof. exact (eq_refl (@eq (_143642 -> Prop))). Qed.
Lemma lem8096197 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term40 _143642 _143649 r s x) = (term41 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096196 _143642) (@lem8096195 _143642 _143649 r s x)). Qed.
Lemma lem8096198 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term37 _143642 _143649 r s x) = (term38 _143642 _143649 r s x).
Proof. exact (eq_refl (term37 _143642 _143649 r s x)). Qed.
Lemma lem8096199 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term36 _143642 _143649 r s x) = (term37 _143642 _143649 r s x)) = ((term37 _143642 _143649 r s x) = (term38 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8096197 _143642 _143649 r s x) (@lem8096198 _143642 _143649 r s x)). Qed.
Lemma lem8096200 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term37 _143642 _143649 r s x) = (term38 _143642 _143649 r s x).
Proof. exact (EQ_MP (@lem8096199 _143642 _143649 r s x) (@lem8096191 _143642 _143649 r s x)). Qed.
Lemma lem8096205 {_143642 : Type'} : (@ε _143642) = (@ε _143642).
Proof. exact (eq_refl (@ε _143642)). Qed.
Lemma lem8096206 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term46 _143642 _143649 r s x) = (term47 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096205 _143642) (@lem8096200 _143642 _143649 r s x)). Qed.
Lemma lem8096207 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term48 _143642 _143649 r s x) = (term49 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096187 _143642 _143649 r s x) (@lem8096206 _143642 _143649 r s x)). Qed.
Lemma lem8096208 {_143642 : Type'} : (term50 _143642) = (term50 _143642).
Proof. exact (eq_refl (term50 _143642)). Qed.
Lemma lem8096209 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term34 _143642 _143649 r s x) = (term51 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096207 _143642 _143649 r s x) (@lem8096208 _143642)). Qed.
Lemma lem8096210 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term26 _143642 _143649 x r s) = (term51 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8096166 _143642 _143649 r s x) (@lem8096209 _143642 _143649 r s x)). Qed.
Lemma lem8096211 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term25 _143642 _143649 x r s) = (term51 _143642 _143649 r s x).
Proof. exact (TRANS (@lem8096153 _143642 _143649 x r s) (@lem8096210 _143642 _143649 r s x)). Qed.
Lemma lem8096212 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8096213 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term52 _143642 _143649 x r s) = (term53 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096212 _143642) (@lem8096211 _143642 _143649 r s x)). Qed.
Lemma lem8096219 {_4656 _4660 : Type'} : (@_MATCH _4656 _4660) = (term0 _4656 _4660).
Proof. exact (@_MATCH_def _4656 _4660). Qed.
Lemma lem8096220 {_143642 _143649 : Type'} : (@_MATCH _143649 _143642) = (term1 _143642 _143649).
Proof. exact (@lem8096219 _143649 _143642). Qed.
Lemma lem8096221 {_143649 : Type'} (x : _143649) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8096222 {_143642 _143649 : Type'} (x : _143649) : (@_MATCH _143649 _143642 x) = (term2 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096220 _143642 _143649) (@lem8096221 _143649 x)). Qed.
Lemma lem8096224 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096225 {_143642 _143649 : Type'} (f : type1450 _143642 _143649) (y : _143649) : (term4 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096224 _143649 (type743 _143642 _143649) f y). Qed.
Lemma lem8096226 {_143642 _143649 : Type'} (x : _143649) : (term5 _143642 _143649 x) = (term2 _143642 _143649 x).
Proof. exact (@lem8096225 _143642 _143649 (term1 _143642 _143649) x). Qed.
Lemma lem8096227 {_143642 _143649 : Type'} (e : _143649) : (term2 _143642 _143649 e) = (term6 _143642 _143649 e).
Proof. exact (eq_refl (term2 _143642 _143649 e)). Qed.
Lemma lem8096228 {_143642 _143649 : Type'} : (term7 _143642 _143649) = (term1 _143642 _143649).
Proof. exact (fun_ext (fun e : _143649 => @lem8096227 _143642 _143649 e)). Qed.
Lemma lem8096229 {_143649 : Type'} (x : _143649) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8096230 {_143642 _143649 : Type'} (x : _143649) : (term5 _143642 _143649 x) = (term2 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096228 _143642 _143649) (@lem8096229 _143649 x)). Qed.
Lemma lem8096231 {_143642 _143649 : Type'} : (@eq ((_143649 -> _143642 -> Prop) -> _143642)) = (@eq ((_143649 -> _143642 -> Prop) -> _143642)).
Proof. exact (eq_refl (@eq ((_143649 -> _143642 -> Prop) -> _143642))). Qed.
Lemma lem8096232 {_143642 _143649 : Type'} (x : _143649) : (term8 _143642 _143649 x) = (term9 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096231 _143642 _143649) (@lem8096230 _143642 _143649 x)). Qed.
Lemma lem8096233 {_143642 _143649 : Type'} (x : _143649) : (term2 _143642 _143649 x) = (term6 _143642 _143649 x).
Proof. exact (eq_refl (term2 _143642 _143649 x)). Qed.
Lemma lem8096234 {_143642 _143649 : Type'} (x : _143649) : ((term5 _143642 _143649 x) = (term2 _143642 _143649 x)) = ((term2 _143642 _143649 x) = (term6 _143642 _143649 x)).
Proof. exact (MK_COMB (@lem8096232 _143642 _143649 x) (@lem8096233 _143642 _143649 x)). Qed.
Lemma lem8096235 {_143642 _143649 : Type'} (x : _143649) : (term2 _143642 _143649 x) = (term6 _143642 _143649 x).
Proof. exact (EQ_MP (@lem8096234 _143642 _143649 x) (@lem8096226 _143642 _143649 x)). Qed.
Lemma lem8096236 {_143642 _143649 : Type'} (x : _143649) : (@_MATCH _143649 _143642 x) = (term6 _143642 _143649 x).
Proof. exact (TRANS (@lem8096222 _143642 _143649 x) (@lem8096235 _143642 _143649 x)). Qed.
Lemma lem8096237 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem8096238 {_143642 _143649 : Type'} (x : _143649) (r : type1470 _143642 _143649) : (@_MATCH _143649 _143642 x r) = (term29 _143642 _143649 x r).
Proof. exact (MK_COMB (@lem8096236 _143642 _143649 x) (@lem8096237 _143642 _143649 r)). Qed.
Lemma lem8096240 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096241 {_143642 _143649 : Type'} (f : type743 _143642 _143649) (y : type1470 _143642 _143649) : (term27 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096240 (type1470 _143642 _143649) _143642 f y). Qed.
Lemma lem8096242 {_143642 _143649 : Type'} (x : _143649) (r : type1470 _143642 _143649) : (term54 _143642 _143649 x r) = (term29 _143642 _143649 x r).
Proof. exact (@lem8096241 _143642 _143649 (term6 _143642 _143649 x) r). Qed.
Lemma lem8096243 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term29 _143642 _143649 x r) = (term30 _143642 _143649 r x).
Proof. exact (eq_refl (term29 _143642 _143649 x r)). Qed.
Lemma lem8096244 {_143642 _143649 : Type'} (x : _143649) : (term31 _143642 _143649 x) = (term6 _143642 _143649 x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8096243 _143642 _143649 r x)). Qed.
Lemma lem8096245 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem8096246 {_143642 _143649 : Type'} (x : _143649) (r : type1470 _143642 _143649) : (term54 _143642 _143649 x r) = (term29 _143642 _143649 x r).
Proof. exact (MK_COMB (@lem8096244 _143642 _143649 x) (@lem8096245 _143642 _143649 r)). Qed.
Lemma lem8096247 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8096248 {_143642 _143649 : Type'} (x : _143649) (r : type1470 _143642 _143649) : (term55 _143642 _143649 x r) = (term56 _143642 _143649 x r).
Proof. exact (MK_COMB (@lem8096247 _143642) (@lem8096246 _143642 _143649 x r)). Qed.
Lemma lem8096249 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term29 _143642 _143649 x r) = (term30 _143642 _143649 r x).
Proof. exact (eq_refl (term29 _143642 _143649 x r)). Qed.
Lemma lem8096250 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : ((term54 _143642 _143649 x r) = (term29 _143642 _143649 x r)) = ((term29 _143642 _143649 x r) = (term30 _143642 _143649 r x)).
Proof. exact (MK_COMB (@lem8096248 _143642 _143649 x r) (@lem8096249 _143642 _143649 r x)). Qed.
Lemma lem8096251 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term29 _143642 _143649 x r) = (term30 _143642 _143649 r x).
Proof. exact (EQ_MP (@lem8096250 _143642 _143649 r x) (@lem8096242 _143642 _143649 x r)). Qed.
Lemma lem8096252 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (@_MATCH _143649 _143642 x r) = (term30 _143642 _143649 r x).
Proof. exact (TRANS (@lem8096238 _143642 _143649 x r) (@lem8096251 _143642 _143649 r x)). Qed.
Lemma lem8096253 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term57 _143642 _143649 r x) = (term57 _143642 _143649 r x).
Proof. exact (eq_refl (term57 _143642 _143649 r x)). Qed.
Lemma lem8096254 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term58 _143642 _143649 x r) = (term59 _143642 _143649 r x).
Proof. exact (MK_COMB (@lem8096253 _143642 _143649 r x) (@lem8096252 _143642 _143649 r x)). Qed.
Lemma lem8096256 {_4656 _4660 : Type'} : (@_MATCH _4656 _4660) = (term0 _4656 _4660).
Proof. exact (@_MATCH_def _4656 _4660). Qed.
Lemma lem8096257 {_143642 _143649 : Type'} : (@_MATCH _143649 _143642) = (term1 _143642 _143649).
Proof. exact (@lem8096256 _143649 _143642). Qed.
Lemma lem8096258 {_143649 : Type'} (x : _143649) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8096259 {_143642 _143649 : Type'} (x : _143649) : (@_MATCH _143649 _143642 x) = (term2 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096257 _143642 _143649) (@lem8096258 _143649 x)). Qed.
Lemma lem8096261 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096262 {_143642 _143649 : Type'} (f : type1450 _143642 _143649) (y : _143649) : (term4 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096261 _143649 (type743 _143642 _143649) f y). Qed.
Lemma lem8096263 {_143642 _143649 : Type'} (x : _143649) : (term5 _143642 _143649 x) = (term2 _143642 _143649 x).
Proof. exact (@lem8096262 _143642 _143649 (term1 _143642 _143649) x). Qed.
Lemma lem8096264 {_143642 _143649 : Type'} (e : _143649) : (term2 _143642 _143649 e) = (term6 _143642 _143649 e).
Proof. exact (eq_refl (term2 _143642 _143649 e)). Qed.
Lemma lem8096265 {_143642 _143649 : Type'} : (term7 _143642 _143649) = (term1 _143642 _143649).
Proof. exact (fun_ext (fun e : _143649 => @lem8096264 _143642 _143649 e)). Qed.
Lemma lem8096266 {_143649 : Type'} (x : _143649) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8096267 {_143642 _143649 : Type'} (x : _143649) : (term5 _143642 _143649 x) = (term2 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096265 _143642 _143649) (@lem8096266 _143649 x)). Qed.
Lemma lem8096268 {_143642 _143649 : Type'} : (@eq ((_143649 -> _143642 -> Prop) -> _143642)) = (@eq ((_143649 -> _143642 -> Prop) -> _143642)).
Proof. exact (eq_refl (@eq ((_143649 -> _143642 -> Prop) -> _143642))). Qed.
Lemma lem8096269 {_143642 _143649 : Type'} (x : _143649) : (term8 _143642 _143649 x) = (term9 _143642 _143649 x).
Proof. exact (MK_COMB (@lem8096268 _143642 _143649) (@lem8096267 _143642 _143649 x)). Qed.
Lemma lem8096270 {_143642 _143649 : Type'} (x : _143649) : (term2 _143642 _143649 x) = (term6 _143642 _143649 x).
Proof. exact (eq_refl (term2 _143642 _143649 x)). Qed.
Lemma lem8096271 {_143642 _143649 : Type'} (x : _143649) : ((term5 _143642 _143649 x) = (term2 _143642 _143649 x)) = ((term2 _143642 _143649 x) = (term6 _143642 _143649 x)).
Proof. exact (MK_COMB (@lem8096269 _143642 _143649 x) (@lem8096270 _143642 _143649 x)). Qed.
Lemma lem8096272 {_143642 _143649 : Type'} (x : _143649) : (term2 _143642 _143649 x) = (term6 _143642 _143649 x).
Proof. exact (EQ_MP (@lem8096271 _143642 _143649 x) (@lem8096263 _143642 _143649 x)). Qed.
Lemma lem8096273 {_143642 _143649 : Type'} (x : _143649) : (@_MATCH _143649 _143642 x) = (term6 _143642 _143649 x).
Proof. exact (TRANS (@lem8096259 _143642 _143649 x) (@lem8096272 _143642 _143649 x)). Qed.
Lemma lem8096274 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem8096275 {_143642 _143649 : Type'} (x : _143649) (s : type1470 _143642 _143649) : (@_MATCH _143649 _143642 x s) = (term29 _143642 _143649 x s).
Proof. exact (MK_COMB (@lem8096273 _143642 _143649 x) (@lem8096274 _143642 _143649 s)). Qed.
Lemma lem8096277 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8096278 {_143642 _143649 : Type'} (f : type743 _143642 _143649) (y : type1470 _143642 _143649) : (term27 _143642 _143649 f y) = (f y).
Proof. exact (@lem8096277 (type1470 _143642 _143649) _143642 f y). Qed.
Lemma lem8096279 {_143642 _143649 : Type'} (x : _143649) (s : type1470 _143642 _143649) : (term54 _143642 _143649 x s) = (term29 _143642 _143649 x s).
Proof. exact (@lem8096278 _143642 _143649 (term6 _143642 _143649 x) s). Qed.
Lemma lem8096280 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) : (term29 _143642 _143649 x r) = (term30 _143642 _143649 r x).
Proof. exact (eq_refl (term29 _143642 _143649 x r)). Qed.
Lemma lem8096281 {_143642 _143649 : Type'} (x : _143649) : (term31 _143642 _143649 x) = (term6 _143642 _143649 x).
Proof. exact (fun_ext (fun r : type1470 _143642 _143649 => @lem8096280 _143642 _143649 r x)). Qed.
Lemma lem8096282 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem8096283 {_143642 _143649 : Type'} (x : _143649) (s : type1470 _143642 _143649) : (term54 _143642 _143649 x s) = (term29 _143642 _143649 x s).
Proof. exact (MK_COMB (@lem8096281 _143642 _143649 x) (@lem8096282 _143642 _143649 s)). Qed.
Lemma lem8096284 {_143642 : Type'} : (@eq _143642) = (@eq _143642).
Proof. exact (eq_refl (@eq _143642)). Qed.
Lemma lem8096285 {_143642 _143649 : Type'} (x : _143649) (s : type1470 _143642 _143649) : (term55 _143642 _143649 x s) = (term56 _143642 _143649 x s).
Proof. exact (MK_COMB (@lem8096284 _143642) (@lem8096283 _143642 _143649 x s)). Qed.
Lemma lem8096286 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term29 _143642 _143649 x s) = (term30 _143642 _143649 s x).
Proof. exact (eq_refl (term29 _143642 _143649 x s)). Qed.
Lemma lem8096287 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : ((term54 _143642 _143649 x s) = (term29 _143642 _143649 x s)) = ((term29 _143642 _143649 x s) = (term30 _143642 _143649 s x)).
Proof. exact (MK_COMB (@lem8096285 _143642 _143649 x s) (@lem8096286 _143642 _143649 s x)). Qed.
Lemma lem8096288 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (term29 _143642 _143649 x s) = (term30 _143642 _143649 s x).
Proof. exact (EQ_MP (@lem8096287 _143642 _143649 s x) (@lem8096279 _143642 _143649 x s)). Qed.
Lemma lem8096289 {_143642 _143649 : Type'} (s : type1470 _143642 _143649) (x : _143649) : (@_MATCH _143649 _143642 x s) = (term30 _143642 _143649 s x).
Proof. exact (TRANS (@lem8096275 _143642 _143649 x s) (@lem8096288 _143642 _143649 s x)). Qed.
Lemma lem8096290 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : (term60 _143642 _143649 r x s) = (term61 _143642 _143649 r s x).
Proof. exact (MK_COMB (@lem8096254 _143642 _143649 r x) (@lem8096289 _143642 _143649 s x)). Qed.
Lemma lem8096291 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (s : type1470 _143642 _143649) (x : _143649) : ((term25 _143642 _143649 x r s) = (term60 _143642 _143649 r x s)) = ((term51 _143642 _143649 r s x) = (term61 _143642 _143649 r s x)).
Proof. exact (MK_COMB (@lem8096213 _143642 _143649 r s x) (@lem8096290 _143642 _143649 r s x)). Qed.
Lemma lem8096294 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (s : type1470 _143642 _143649) : ((term51 _143642 _143649 r s x) = (term61 _143642 _143649 r s x)) = ((term25 _143642 _143649 x r s) = (term60 _143642 _143649 r x s)).
Proof. exact (SYM (@lem8096291 _143642 _143649 r s x)). Qed.
