Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1100408_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1100145 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1100146 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1100147 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1100146 A B f) (@lem1100145 A B f)). Qed.
Lemma lem1100148 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1100147 A B f y). Qed.
Lemma lem1100149 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1100152 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : ALL' = (term4 _25307 _17969).
Proof. exact (h1). Qed.
Lemma lem1100153 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100154 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P) = (term5 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100152 _25307 ALL' _17969 h1) (@lem1100153 _25307 P)). Qed.
Lemma lem1100156 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100149 A B f y) (@lem1100148 A B f y)). Qed.
Lemma lem1100157 {_25307 : Type'} (f : type663 _25307) (y : _25307 -> Prop) : (term6 _25307 f y) = (f y).
Proof. exact (@lem1100156 (_25307 -> Prop) (type1143 _25307) f y). Qed.
Lemma lem1100158 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term7 _25307 _17969 P) = (term5 _25307 _17969 P).
Proof. exact (@lem1100157 _25307 (term4 _25307 _17969) P). Qed.
Lemma lem1100159 {_25307 : Type'} (_17969 : type1131 _25307) (_17967 : _25307 -> Prop) : (term5 _25307 _17969 _17967) = (term8 _25307 _17969 _17967).
Proof. exact (eq_refl (term5 _25307 _17969 _17967)). Qed.
Lemma lem1100160 {_25307 : Type'} (_17969 : type1131 _25307) : (term9 _25307 _17969) = (term4 _25307 _17969).
Proof. exact (fun_ext (fun _17967 : _25307 -> Prop => @lem1100159 _25307 _17969 _17967)). Qed.
Lemma lem1100161 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100162 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term7 _25307 _17969 P) = (term5 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100160 _25307 _17969) (@lem1100161 _25307 P)). Qed.
Lemma lem1100163 {_25307 : Type'} : (@eq ((list _25307) -> Prop)) = (@eq ((list _25307) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25307) -> Prop))). Qed.
Lemma lem1100164 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term10 _25307 _17969 P) = (term11 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100163 _25307) (@lem1100162 _25307 _17969 P)). Qed.
Lemma lem1100165 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term5 _25307 _17969 P) = (term8 _25307 _17969 P).
Proof. exact (eq_refl (term5 _25307 _17969 P)). Qed.
Lemma lem1100166 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : ((term7 _25307 _17969 P) = (term5 _25307 _17969 P)) = ((term5 _25307 _17969 P) = (term8 _25307 _17969 P)).
Proof. exact (MK_COMB (@lem1100164 _25307 _17969 P) (@lem1100165 _25307 _17969 P)). Qed.
Lemma lem1100167 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term5 _25307 _17969 P) = (term8 _25307 _17969 P).
Proof. exact (EQ_MP (@lem1100166 _25307 _17969 P) (@lem1100158 _25307 _17969 P)). Qed.
Lemma lem1100168 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P) = (term8 _25307 _17969 P).
Proof. exact (TRANS (@lem1100154 _25307 P ALL' _17969 h1) (@lem1100167 _25307 _17969 P)). Qed.
Lemma lem1100169 {_25307 : Type'} : (@nil _25307) = (@nil _25307).
Proof. exact (eq_refl (@nil _25307)). Qed.
Lemma lem1100170 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P (@nil _25307)) = (term12 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100168 _25307 P ALL' _17969 h1) (@lem1100169 _25307)). Qed.
Lemma lem1100172 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100149 A B f y) (@lem1100148 A B f y)). Qed.
Lemma lem1100173 {_25307 : Type'} (f : type1143 _25307) (y : list _25307) : (term13 _25307 f y) = (f y).
Proof. exact (@lem1100172 (list _25307) Prop f y). Qed.
Lemma lem1100174 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term14 _25307 _17969 P) = (term12 _25307 _17969 P).
Proof. exact (@lem1100173 _25307 (term8 _25307 _17969 P) (@nil _25307)). Qed.
Lemma lem1100175 {_25307 : Type'} (_17969 : type1131 _25307) (_17968 : list _25307) (P : _25307 -> Prop) : (term15 _25307 _17969 P _17968) = (_17969 _17968 P).
Proof. exact (eq_refl (term15 _25307 _17969 P _17968)). Qed.
Lemma lem1100176 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term16 _25307 _17969 P) = (term8 _25307 _17969 P).
Proof. exact (fun_ext (fun _17968 : list _25307 => @lem1100175 _25307 _17969 _17968 P)). Qed.
Lemma lem1100177 {_25307 : Type'} : (@nil _25307) = (@nil _25307).
Proof. exact (eq_refl (@nil _25307)). Qed.
Lemma lem1100178 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term14 _25307 _17969 P) = (term12 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100176 _25307 _17969 P) (@lem1100177 _25307)). Qed.
Lemma lem1100179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100180 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term17 _25307 _17969 P) = (term18 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100179) (@lem1100178 _25307 _17969 P)). Qed.
Lemma lem1100181 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term12 _25307 _17969 P) = (_17969 (@nil _25307) P).
Proof. exact (eq_refl (term12 _25307 _17969 P)). Qed.
Lemma lem1100182 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : ((term14 _25307 _17969 P) = (term12 _25307 _17969 P)) = ((term12 _25307 _17969 P) = (_17969 (@nil _25307) P)).
Proof. exact (MK_COMB (@lem1100180 _25307 _17969 P) (@lem1100181 _25307 _17969 P)). Qed.
Lemma lem1100183 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term12 _25307 _17969 P) = (_17969 (@nil _25307) P).
Proof. exact (EQ_MP (@lem1100182 _25307 _17969 P) (@lem1100174 _25307 _17969 P)). Qed.
Lemma lem1100184 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P (@nil _25307)) = (_17969 (@nil _25307) P).
Proof. exact (TRANS (@lem1100170 _25307 P ALL' _17969 h1) (@lem1100183 _25307 _17969 P)). Qed.
Lemma lem1100185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100186 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term19 _25307 ALL' P) = (term20 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100185) (@lem1100184 _25307 P ALL' _17969 h1)). Qed.
Lemma lem1100187 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1100188 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : ((ALL' P (@nil _25307)) = True) = ((_17969 (@nil _25307) P) = True).
Proof. exact (MK_COMB (@lem1100186 _25307 P ALL' _17969 h1) (@lem1100187)). Qed.
Lemma lem1100189 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term21 _25307 ALL') = (term22 _25307 _17969).
Proof. exact (fun_ext (fun P : _25307 -> Prop => @lem1100188 _25307 P ALL' _17969 h1)). Qed.
Lemma lem1100190 {_25307 : Type'} : (@all (_25307 -> Prop)) = (@all (_25307 -> Prop)).
Proof. exact (eq_refl (@all (_25307 -> Prop))). Qed.
Lemma lem1100191 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term23 _25307 ALL') = (term24 _25307 _17969).
Proof. exact (MK_COMB (@lem1100190 _25307) (@lem1100189 _25307 ALL' _17969 h1)). Qed.
Lemma lem1100192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1100193 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term25 _25307 ALL') = (term26 _25307 _17969).
Proof. exact (MK_COMB (@lem1100192) (@lem1100191 _25307 ALL' _17969 h1)). Qed.
Lemma lem1100195 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : ALL' = (term4 _25307 _17969).
Proof. exact (h1). Qed.
Lemma lem1100196 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100197 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P) = (term5 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100195 _25307 ALL' _17969 h1) (@lem1100196 _25307 P)). Qed.
Lemma lem1100199 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100149 A B f y) (@lem1100148 A B f y)). Qed.
Lemma lem1100200 {_25307 : Type'} (f : type663 _25307) (y : _25307 -> Prop) : (term6 _25307 f y) = (f y).
Proof. exact (@lem1100199 (_25307 -> Prop) (type1143 _25307) f y). Qed.
Lemma lem1100201 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term7 _25307 _17969 P) = (term5 _25307 _17969 P).
Proof. exact (@lem1100200 _25307 (term4 _25307 _17969) P). Qed.
Lemma lem1100202 {_25307 : Type'} (_17969 : type1131 _25307) (_17967 : _25307 -> Prop) : (term5 _25307 _17969 _17967) = (term8 _25307 _17969 _17967).
Proof. exact (eq_refl (term5 _25307 _17969 _17967)). Qed.
Lemma lem1100203 {_25307 : Type'} (_17969 : type1131 _25307) : (term9 _25307 _17969) = (term4 _25307 _17969).
Proof. exact (fun_ext (fun _17967 : _25307 -> Prop => @lem1100202 _25307 _17969 _17967)). Qed.
Lemma lem1100204 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100205 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term7 _25307 _17969 P) = (term5 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100203 _25307 _17969) (@lem1100204 _25307 P)). Qed.
Lemma lem1100206 {_25307 : Type'} : (@eq ((list _25307) -> Prop)) = (@eq ((list _25307) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25307) -> Prop))). Qed.
Lemma lem1100207 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term10 _25307 _17969 P) = (term11 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100206 _25307) (@lem1100205 _25307 _17969 P)). Qed.
Lemma lem1100208 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term5 _25307 _17969 P) = (term8 _25307 _17969 P).
Proof. exact (eq_refl (term5 _25307 _17969 P)). Qed.
Lemma lem1100209 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : ((term7 _25307 _17969 P) = (term5 _25307 _17969 P)) = ((term5 _25307 _17969 P) = (term8 _25307 _17969 P)).
Proof. exact (MK_COMB (@lem1100207 _25307 _17969 P) (@lem1100208 _25307 _17969 P)). Qed.
Lemma lem1100210 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term5 _25307 _17969 P) = (term8 _25307 _17969 P).
Proof. exact (EQ_MP (@lem1100209 _25307 _17969 P) (@lem1100201 _25307 _17969 P)). Qed.
Lemma lem1100211 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P) = (term8 _25307 _17969 P).
Proof. exact (TRANS (@lem1100197 _25307 P ALL' _17969 h1) (@lem1100210 _25307 _17969 P)). Qed.
Lemma lem1100212 {_25307 : Type'} (h : _25307) (t : list _25307) : (@cons _25307 h t) = (@cons _25307 h t).
Proof. exact (eq_refl (@cons _25307 h t)). Qed.
Lemma lem1100213 {_25307 : Type'} (P : _25307 -> Prop) (h : _25307) (t : list _25307) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term27 _25307 ALL' P h t) = (term28 _25307 _17969 P h t).
Proof. exact (MK_COMB (@lem1100211 _25307 P ALL' _17969 h1) (@lem1100212 _25307 h t)). Qed.
Lemma lem1100215 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100149 A B f y) (@lem1100148 A B f y)). Qed.
Lemma lem1100216 {_25307 : Type'} (f : type1143 _25307) (y : list _25307) : (term13 _25307 f y) = (f y).
Proof. exact (@lem1100215 (list _25307) Prop f y). Qed.
Lemma lem1100217 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) (h : _25307) (t : list _25307) : (term29 _25307 _17969 P h t) = (term28 _25307 _17969 P h t).
Proof. exact (@lem1100216 _25307 (term8 _25307 _17969 P) (@cons _25307 h t)). Qed.
Lemma lem1100218 {_25307 : Type'} (_17969 : type1131 _25307) (_17968 : list _25307) (P : _25307 -> Prop) : (term15 _25307 _17969 P _17968) = (_17969 _17968 P).
Proof. exact (eq_refl (term15 _25307 _17969 P _17968)). Qed.
Lemma lem1100219 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term16 _25307 _17969 P) = (term8 _25307 _17969 P).
Proof. exact (fun_ext (fun _17968 : list _25307 => @lem1100218 _25307 _17969 _17968 P)). Qed.
Lemma lem1100220 {_25307 : Type'} (h : _25307) (t : list _25307) : (@cons _25307 h t) = (@cons _25307 h t).
Proof. exact (eq_refl (@cons _25307 h t)). Qed.
Lemma lem1100221 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) (h : _25307) (t : list _25307) : (term29 _25307 _17969 P h t) = (term28 _25307 _17969 P h t).
Proof. exact (MK_COMB (@lem1100219 _25307 _17969 P) (@lem1100220 _25307 h t)). Qed.
Lemma lem1100222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100223 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) (h : _25307) (t : list _25307) : (term30 _25307 _17969 P h t) = (term31 _25307 _17969 P h t).
Proof. exact (MK_COMB (@lem1100222) (@lem1100221 _25307 _17969 P h t)). Qed.
Lemma lem1100224 {_25307 : Type'} (_17969 : type1131 _25307) (h : _25307) (t : list _25307) (P : _25307 -> Prop) : (term28 _25307 _17969 P h t) = (term32 _25307 _17969 h t P).
Proof. exact (eq_refl (term28 _25307 _17969 P h t)). Qed.
Lemma lem1100225 {_25307 : Type'} (_17969 : type1131 _25307) (h : _25307) (t : list _25307) (P : _25307 -> Prop) : ((term29 _25307 _17969 P h t) = (term28 _25307 _17969 P h t)) = ((term28 _25307 _17969 P h t) = (term32 _25307 _17969 h t P)).
Proof. exact (MK_COMB (@lem1100223 _25307 _17969 P h t) (@lem1100224 _25307 _17969 h t P)). Qed.
Lemma lem1100226 {_25307 : Type'} (_17969 : type1131 _25307) (h : _25307) (t : list _25307) (P : _25307 -> Prop) : (term28 _25307 _17969 P h t) = (term32 _25307 _17969 h t P).
Proof. exact (EQ_MP (@lem1100225 _25307 _17969 h t P) (@lem1100217 _25307 _17969 P h t)). Qed.
Lemma lem1100227 {_25307 : Type'} (h : _25307) (t : list _25307) (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term27 _25307 ALL' P h t) = (term32 _25307 _17969 h t P).
Proof. exact (TRANS (@lem1100213 _25307 P h t ALL' _17969 h1) (@lem1100226 _25307 _17969 h t P)). Qed.
Lemma lem1100228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100229 {_25307 : Type'} (h : _25307) (t : list _25307) (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term33 _25307 ALL' P h t) = (term34 _25307 _17969 h t P).
Proof. exact (MK_COMB (@lem1100228) (@lem1100227 _25307 h t P ALL' _17969 h1)). Qed.
Lemma lem1100231 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : ALL' = (term4 _25307 _17969).
Proof. exact (h1). Qed.
Lemma lem1100232 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100233 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P) = (term5 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100231 _25307 ALL' _17969 h1) (@lem1100232 _25307 P)). Qed.
Lemma lem1100235 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100149 A B f y) (@lem1100148 A B f y)). Qed.
Lemma lem1100236 {_25307 : Type'} (f : type663 _25307) (y : _25307 -> Prop) : (term6 _25307 f y) = (f y).
Proof. exact (@lem1100235 (_25307 -> Prop) (type1143 _25307) f y). Qed.
Lemma lem1100237 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term7 _25307 _17969 P) = (term5 _25307 _17969 P).
Proof. exact (@lem1100236 _25307 (term4 _25307 _17969) P). Qed.
Lemma lem1100238 {_25307 : Type'} (_17969 : type1131 _25307) (_17967 : _25307 -> Prop) : (term5 _25307 _17969 _17967) = (term8 _25307 _17969 _17967).
Proof. exact (eq_refl (term5 _25307 _17969 _17967)). Qed.
Lemma lem1100239 {_25307 : Type'} (_17969 : type1131 _25307) : (term9 _25307 _17969) = (term4 _25307 _17969).
Proof. exact (fun_ext (fun _17967 : _25307 -> Prop => @lem1100238 _25307 _17969 _17967)). Qed.
Lemma lem1100240 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100241 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term7 _25307 _17969 P) = (term5 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100239 _25307 _17969) (@lem1100240 _25307 P)). Qed.
Lemma lem1100242 {_25307 : Type'} : (@eq ((list _25307) -> Prop)) = (@eq ((list _25307) -> Prop)).
Proof. exact (eq_refl (@eq ((list _25307) -> Prop))). Qed.
Lemma lem1100243 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term10 _25307 _17969 P) = (term11 _25307 _17969 P).
Proof. exact (MK_COMB (@lem1100242 _25307) (@lem1100241 _25307 _17969 P)). Qed.
Lemma lem1100244 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term5 _25307 _17969 P) = (term8 _25307 _17969 P).
Proof. exact (eq_refl (term5 _25307 _17969 P)). Qed.
Lemma lem1100245 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : ((term7 _25307 _17969 P) = (term5 _25307 _17969 P)) = ((term5 _25307 _17969 P) = (term8 _25307 _17969 P)).
Proof. exact (MK_COMB (@lem1100243 _25307 _17969 P) (@lem1100244 _25307 _17969 P)). Qed.
Lemma lem1100246 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term5 _25307 _17969 P) = (term8 _25307 _17969 P).
Proof. exact (EQ_MP (@lem1100245 _25307 _17969 P) (@lem1100237 _25307 _17969 P)). Qed.
Lemma lem1100247 {_25307 : Type'} (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P) = (term8 _25307 _17969 P).
Proof. exact (TRANS (@lem1100233 _25307 P ALL' _17969 h1) (@lem1100246 _25307 _17969 P)). Qed.
Lemma lem1100248 {_25307 : Type'} (t : list _25307) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1100249 {_25307 : Type'} (P : _25307 -> Prop) (t : list _25307) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P t) = (term15 _25307 _17969 P t).
Proof. exact (MK_COMB (@lem1100247 _25307 P ALL' _17969 h1) (@lem1100248 _25307 t)). Qed.
Lemma lem1100251 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1100149 A B f y) (@lem1100148 A B f y)). Qed.
Lemma lem1100252 {_25307 : Type'} (f : type1143 _25307) (y : list _25307) : (term13 _25307 f y) = (f y).
Proof. exact (@lem1100251 (list _25307) Prop f y). Qed.
Lemma lem1100253 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) (t : list _25307) : (term35 _25307 _17969 P t) = (term15 _25307 _17969 P t).
Proof. exact (@lem1100252 _25307 (term8 _25307 _17969 P) t). Qed.
Lemma lem1100254 {_25307 : Type'} (_17969 : type1131 _25307) (_17968 : list _25307) (P : _25307 -> Prop) : (term15 _25307 _17969 P _17968) = (_17969 _17968 P).
Proof. exact (eq_refl (term15 _25307 _17969 P _17968)). Qed.
Lemma lem1100255 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term16 _25307 _17969 P) = (term8 _25307 _17969 P).
Proof. exact (fun_ext (fun _17968 : list _25307 => @lem1100254 _25307 _17969 _17968 P)). Qed.
Lemma lem1100256 {_25307 : Type'} (t : list _25307) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1100257 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) (t : list _25307) : (term35 _25307 _17969 P t) = (term15 _25307 _17969 P t).
Proof. exact (MK_COMB (@lem1100255 _25307 _17969 P) (@lem1100256 _25307 t)). Qed.
Lemma lem1100258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100259 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) (t : list _25307) : (term36 _25307 _17969 P t) = (term37 _25307 _17969 P t).
Proof. exact (MK_COMB (@lem1100258) (@lem1100257 _25307 _17969 P t)). Qed.
Lemma lem1100260 {_25307 : Type'} (_17969 : type1131 _25307) (t : list _25307) (P : _25307 -> Prop) : (term15 _25307 _17969 P t) = (_17969 t P).
Proof. exact (eq_refl (term15 _25307 _17969 P t)). Qed.
Lemma lem1100261 {_25307 : Type'} (_17969 : type1131 _25307) (t : list _25307) (P : _25307 -> Prop) : ((term35 _25307 _17969 P t) = (term15 _25307 _17969 P t)) = ((term15 _25307 _17969 P t) = (_17969 t P)).
Proof. exact (MK_COMB (@lem1100259 _25307 _17969 P t) (@lem1100260 _25307 _17969 t P)). Qed.
Lemma lem1100262 {_25307 : Type'} (_17969 : type1131 _25307) (t : list _25307) (P : _25307 -> Prop) : (term15 _25307 _17969 P t) = (_17969 t P).
Proof. exact (EQ_MP (@lem1100261 _25307 _17969 t P) (@lem1100253 _25307 _17969 P t)). Qed.
Lemma lem1100263 {_25307 : Type'} (t : list _25307) (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (ALL' P t) = (_17969 t P).
Proof. exact (TRANS (@lem1100249 _25307 P t ALL' _17969 h1) (@lem1100262 _25307 _17969 t P)). Qed.
Lemma lem1100264 {_25307 : Type'} (P : _25307 -> Prop) (h : _25307) : (term38 _25307 P h) = (term38 _25307 P h).
Proof. exact (eq_refl (term38 _25307 P h)). Qed.
Lemma lem1100265 {_25307 : Type'} (h : _25307) (t : list _25307) (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term39 _25307 h ALL' P t) = (term40 _25307 h _17969 t P).
Proof. exact (MK_COMB (@lem1100264 _25307 P h) (@lem1100263 _25307 t P ALL' _17969 h1)). Qed.
Lemma lem1100266 {_25307 : Type'} (h : _25307) (t : list _25307) (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : ((term27 _25307 ALL' P h t) = (term39 _25307 h ALL' P t)) = ((term32 _25307 _17969 h t P) = (term40 _25307 h _17969 t P)).
Proof. exact (MK_COMB (@lem1100229 _25307 h t P ALL' _17969 h1) (@lem1100265 _25307 h t P ALL' _17969 h1)). Qed.
Lemma lem1100267 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term41 _25307 h ALL' P) = (term42 _25307 h _17969 P).
Proof. exact (fun_ext (fun t : list _25307 => @lem1100266 _25307 h t P ALL' _17969 h1)). Qed.
Lemma lem1100268 {_25307 : Type'} : (@all (list _25307)) = (@all (list _25307)).
Proof. exact (eq_refl (@all (list _25307))). Qed.
Lemma lem1100269 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term43 _25307 h ALL' P) = (term44 _25307 h _17969 P).
Proof. exact (MK_COMB (@lem1100268 _25307) (@lem1100267 _25307 h P ALL' _17969 h1)). Qed.
Lemma lem1100270 {_25307 : Type'} (h : _25307) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term45 _25307 h ALL') = (term46 _25307 h _17969).
Proof. exact (fun_ext (fun P : _25307 -> Prop => @lem1100269 _25307 h P ALL' _17969 h1)). Qed.
Lemma lem1100271 {_25307 : Type'} : (@all (_25307 -> Prop)) = (@all (_25307 -> Prop)).
Proof. exact (eq_refl (@all (_25307 -> Prop))). Qed.
Lemma lem1100272 {_25307 : Type'} (h : _25307) (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term47 _25307 h ALL') = (term48 _25307 h _17969).
Proof. exact (MK_COMB (@lem1100271 _25307) (@lem1100270 _25307 h ALL' _17969 h1)). Qed.
Lemma lem1100273 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term49 _25307 ALL') = (term50 _25307 _17969).
Proof. exact (fun_ext (fun h : _25307 => @lem1100272 _25307 h ALL' _17969 h1)). Qed.
Lemma lem1100274 {_25307 : Type'} : (@all _25307) = (@all _25307).
Proof. exact (eq_refl (@all _25307)). Qed.
Lemma lem1100275 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term51 _25307 ALL') = (term52 _25307 _17969).
Proof. exact (MK_COMB (@lem1100274 _25307) (@lem1100273 _25307 ALL' _17969 h1)). Qed.
Lemma lem1100276 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term53 _25307 ALL') = (term54 _25307 _17969).
Proof. exact (MK_COMB (@lem1100193 _25307 ALL' _17969 h1) (@lem1100275 _25307 ALL' _17969 h1)). Qed.
Lemma lem1100277 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : (_17969 (@nil _25307)) = (term55 _25307)) : (_17969 (@nil _25307)) = (term55 _25307).
Proof. exact (h1). Qed.
Lemma lem1100278 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100279 {_25307 : Type'} (P : _25307 -> Prop) (_17969 : type1131 _25307) (h1 : (_17969 (@nil _25307)) = (term55 _25307)) : (_17969 (@nil _25307) P) = (term56 _25307 P).
Proof. exact (MK_COMB (@lem1100277 _25307 _17969 h1) (@lem1100278 _25307 P)). Qed.
Lemma lem1100280 {_25307 : Type'} (P : _25307 -> Prop) : (term56 _25307 P) = True.
Proof. exact (eq_refl (term56 _25307 P)). Qed.
Lemma lem1100281 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : (term20 _25307 _17969 P) = (term20 _25307 _17969 P).
Proof. exact (eq_refl (term20 _25307 _17969 P)). Qed.
Lemma lem1100282 {_25307 : Type'} (_17969 : type1131 _25307) (P : _25307 -> Prop) : ((_17969 (@nil _25307) P) = (term56 _25307 P)) = ((_17969 (@nil _25307) P) = True).
Proof. exact (MK_COMB (@lem1100281 _25307 _17969 P) (@lem1100280 _25307 P)). Qed.
Lemma lem1100283 {_25307 : Type'} (P : _25307 -> Prop) (_17969 : type1131 _25307) (h1 : (_17969 (@nil _25307)) = (term55 _25307)) : (_17969 (@nil _25307) P) = True.
Proof. exact (EQ_MP (@lem1100282 _25307 _17969 P) (@lem1100279 _25307 P _17969 h1)). Qed.
Lemma lem1100284 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : (_17969 (@nil _25307)) = (term55 _25307)) : term24 _25307 _17969.
Proof. exact (fun P : _25307 -> Prop => @lem1100283 _25307 P _17969 h1). Qed.
Lemma lem1100285 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : term57 _25307 _17969.
Proof. exact (h1). Qed.
Lemma lem1100286 {_25307 : Type'} (h : _25307) (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : term58 _25307 _17969 h.
Proof. exact (@lem1100285 _25307 _17969 h1 h). Qed.
Lemma lem1100287 {_25307 : Type'} (h : _25307) (_17969 : type1131 _25307) : (term58 _25307 _17969 h) = (term59 _25307 h _17969).
Proof. exact (eq_refl (term58 _25307 _17969 h)). Qed.
Lemma lem1100288 {_25307 : Type'} (h : _25307) (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : term59 _25307 h _17969.
Proof. exact (EQ_MP (@lem1100287 _25307 h _17969) (@lem1100286 _25307 h _17969 h1)). Qed.
Lemma lem1100289 {_25307 : Type'} (h : _25307) (t : list _25307) (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : term60 _25307 h _17969 t.
Proof. exact (@lem1100288 _25307 h _17969 h1 t). Qed.
Lemma lem1100290 {_25307 : Type'} (h : _25307) (_17969 : type1131 _25307) (t : list _25307) : (term60 _25307 h _17969 t) = ((term61 _25307 _17969 h t) = (term62 _25307 h _17969 t)).
Proof. exact (eq_refl (term60 _25307 h _17969 t)). Qed.
Lemma lem1100291 {_25307 : Type'} (h : _25307) (t : list _25307) (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : (term61 _25307 _17969 h t) = (term62 _25307 h _17969 t).
Proof. exact (EQ_MP (@lem1100290 _25307 h _17969 t) (@lem1100289 _25307 h t _17969 h1)). Qed.
Lemma lem1100292 {_25307 : Type'} (P : _25307 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1100293 {_25307 : Type'} (h : _25307) (t : list _25307) (P : _25307 -> Prop) (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : (term32 _25307 _17969 h t P) = (term63 _25307 h _17969 t P).
Proof. exact (MK_COMB (@lem1100291 _25307 h t _17969 h1) (@lem1100292 _25307 P)). Qed.
Lemma lem1100294 {_25307 : Type'} (h : _25307) (_17969 : type1131 _25307) (t : list _25307) (P : _25307 -> Prop) : (term63 _25307 h _17969 t P) = (term40 _25307 h _17969 t P).
Proof. exact (eq_refl (term63 _25307 h _17969 t P)). Qed.
Lemma lem1100295 {_25307 : Type'} (_17969 : type1131 _25307) (h : _25307) (t : list _25307) (P : _25307 -> Prop) : (term34 _25307 _17969 h t P) = (term34 _25307 _17969 h t P).
Proof. exact (eq_refl (term34 _25307 _17969 h t P)). Qed.
Lemma lem1100296 {_25307 : Type'} (h : _25307) (_17969 : type1131 _25307) (t : list _25307) (P : _25307 -> Prop) : ((term32 _25307 _17969 h t P) = (term63 _25307 h _17969 t P)) = ((term32 _25307 _17969 h t P) = (term40 _25307 h _17969 t P)).
Proof. exact (MK_COMB (@lem1100295 _25307 _17969 h t P) (@lem1100294 _25307 h _17969 t P)). Qed.
Lemma lem1100297 {_25307 : Type'} (h : _25307) (t : list _25307) (P : _25307 -> Prop) (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : (term32 _25307 _17969 h t P) = (term40 _25307 h _17969 t P).
Proof. exact (EQ_MP (@lem1100296 _25307 h _17969 t P) (@lem1100293 _25307 h t P _17969 h1)). Qed.
Lemma lem1100298 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : term44 _25307 h _17969 P.
Proof. exact (fun t : list _25307 => @lem1100297 _25307 h t P _17969 h1). Qed.
Lemma lem1100299 {_25307 : Type'} (h : _25307) (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : term48 _25307 h _17969.
Proof. exact (fun P : _25307 -> Prop => @lem1100298 _25307 h P _17969 h1). Qed.
Lemma lem1100300 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term57 _25307 _17969) : term52 _25307 _17969.
Proof. exact (fun h : _25307 => @lem1100299 _25307 h _17969 h1). Qed.
Lemma lem1100301 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term64 _25307 _17969.
Proof. exact (h1). Qed.
Lemma lem1100302 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term57 _25307 _17969.
Proof. exact (proj2 (@lem1100301 _25307 _17969 h1)). Qed.
Lemma lem1100303 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : (_17969 (@nil _25307)) = (term55 _25307).
Proof. exact (proj1 (@lem1100301 _25307 _17969 h1)). Qed.
Lemma lem1100304 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : ((_17969 (@nil _25307)) = (term55 _25307)) = (term24 _25307 _17969).
Proof. exact (prop_ext (fun h2 : (_17969 (@nil _25307)) = (term55 _25307) => @lem1100284 _25307 _17969 h2) (fun h2 : term24 _25307 _17969 => @lem1100303 _25307 _17969 h1)). Qed.
Lemma lem1100305 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term24 _25307 _17969.
Proof. exact (EQ_MP (@lem1100304 _25307 _17969 h1) (@lem1100303 _25307 _17969 h1)). Qed.
Lemma lem1100306 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : (term57 _25307 _17969) = (term52 _25307 _17969).
Proof. exact (prop_ext (fun h2 : term57 _25307 _17969 => @lem1100300 _25307 _17969 h2) (fun h2 : term52 _25307 _17969 => @lem1100302 _25307 _17969 h1)). Qed.
Lemma lem1100307 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term52 _25307 _17969.
Proof. exact (EQ_MP (@lem1100306 _25307 _17969 h1) (@lem1100302 _25307 _17969 h1)). Qed.
Lemma lem1100308 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term54 _25307 _17969.
Proof. exact (conj (@lem1100305 _25307 _17969 h1) (@lem1100307 _25307 _17969 h1)). Qed.
Lemma lem1100309 {A Z : Type'} (NIL' : Z) : term65 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1100310 {A Z : Type'} (NIL' : Z) : (term65 A Z NIL') = (term66 A Z NIL').
Proof. exact (eq_refl (term65 A Z NIL')). Qed.
Lemma lem1100311 {A Z : Type'} (NIL' : Z) : term66 A Z NIL'.
Proof. exact (EQ_MP (@lem1100310 A Z NIL') (@lem1100309 A Z NIL')). Qed.
Lemma lem1100312 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term67 A Z NIL' CONS'.
Proof. exact (@lem1100311 A Z NIL' CONS'). Qed.
Lemma lem1100313 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term67 A Z NIL' CONS') = (term68 A Z NIL' CONS').
Proof. exact (eq_refl (term67 A Z NIL' CONS')). Qed.
Lemma lem1100314 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term68 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1100313 A Z NIL' CONS') (@lem1100312 A Z NIL' CONS')). Qed.
Lemma lem1100315 {_25307 : Type'} (NIL' : type686 _25307) (CONS' : type1387 _25307) : term69 _25307 NIL' CONS'.
Proof. exact (@lem1100314 _25307 (type686 _25307) NIL' CONS'). Qed.
Lemma lem1100316 {_25307 : Type'} : term70 _25307.
Proof. exact (@lem1100315 _25307 (term55 _25307) (term71 _25307)). Qed.
Lemma lem1100317 {_25307 : Type'} (a0 : _25307) : (term72 _25307 a0) = (term73 _25307 a0).
Proof. exact (eq_refl (term72 _25307 a0)). Qed.
Lemma lem1100318 {_25307 : Type'} (a1 : list _25307) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1100319 {_25307 : Type'} (a0 : _25307) (a1 : list _25307) : (term74 _25307 a0 a1) = (term75 _25307 a0 a1).
Proof. exact (MK_COMB (@lem1100317 _25307 a0) (@lem1100318 _25307 a1)). Qed.
Lemma lem1100320 {_25307 : Type'} (a1 : list _25307) (a0 : _25307) : (term75 _25307 a0 a1) = (term76 _25307 a0).
Proof. exact (eq_refl (term75 _25307 a0 a1)). Qed.
Lemma lem1100321 {_25307 : Type'} (a1 : list _25307) (a0 : _25307) : (term74 _25307 a0 a1) = (term76 _25307 a0).
Proof. exact (TRANS (@lem1100319 _25307 a0 a1) (@lem1100320 _25307 a1 a0)). Qed.
Lemma lem1100322 {_25307 : Type'} (fn : type1131 _25307) (a1 : list _25307) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1100323 {_25307 : Type'} (a0 : _25307) (fn : type1131 _25307) (a1 : list _25307) : (term77 _25307 a0 fn a1) = (term78 _25307 a0 fn a1).
Proof. exact (MK_COMB (@lem1100321 _25307 a1 a0) (@lem1100322 _25307 fn a1)). Qed.
Lemma lem1100324 {_25307 : Type'} (a0 : _25307) (fn : type1131 _25307) (a1 : list _25307) : (term78 _25307 a0 fn a1) = (term62 _25307 a0 fn a1).
Proof. exact (eq_refl (term78 _25307 a0 fn a1)). Qed.
Lemma lem1100325 {_25307 : Type'} (a0 : _25307) (fn : type1131 _25307) (a1 : list _25307) : (term77 _25307 a0 fn a1) = (term62 _25307 a0 fn a1).
Proof. exact (TRANS (@lem1100323 _25307 a0 fn a1) (@lem1100324 _25307 a0 fn a1)). Qed.
Lemma lem1100326 {_25307 : Type'} (fn : type1131 _25307) (a0 : _25307) (a1 : list _25307) : (term79 _25307 fn a0 a1) = (term79 _25307 fn a0 a1).
Proof. exact (eq_refl (term79 _25307 fn a0 a1)). Qed.
Lemma lem1100327 {_25307 : Type'} (a0 : _25307) (fn : type1131 _25307) (a1 : list _25307) : ((term61 _25307 fn a0 a1) = (term77 _25307 a0 fn a1)) = ((term61 _25307 fn a0 a1) = (term62 _25307 a0 fn a1)).
Proof. exact (MK_COMB (@lem1100326 _25307 fn a0 a1) (@lem1100325 _25307 a0 fn a1)). Qed.
Lemma lem1100328 {_25307 : Type'} (a0 : _25307) (fn : type1131 _25307) : (term80 _25307 a0 fn) = (term81 _25307 a0 fn).
Proof. exact (fun_ext (fun a1 : list _25307 => @lem1100327 _25307 a0 fn a1)). Qed.
Lemma lem1100329 {_25307 : Type'} : (@all (list _25307)) = (@all (list _25307)).
Proof. exact (eq_refl (@all (list _25307))). Qed.
Lemma lem1100330 {_25307 : Type'} (a0 : _25307) (fn : type1131 _25307) : (term82 _25307 a0 fn) = (term59 _25307 a0 fn).
Proof. exact (MK_COMB (@lem1100329 _25307) (@lem1100328 _25307 a0 fn)). Qed.
Lemma lem1100331 {_25307 : Type'} (fn : type1131 _25307) : (term83 _25307 fn) = (term84 _25307 fn).
Proof. exact (fun_ext (fun a0 : _25307 => @lem1100330 _25307 a0 fn)). Qed.
Lemma lem1100332 {_25307 : Type'} : (@all _25307) = (@all _25307).
Proof. exact (eq_refl (@all _25307)). Qed.
Lemma lem1100333 {_25307 : Type'} (fn : type1131 _25307) : (term85 _25307 fn) = (term57 _25307 fn).
Proof. exact (MK_COMB (@lem1100332 _25307) (@lem1100331 _25307 fn)). Qed.
Lemma lem1100334 {_25307 : Type'} (fn : type1131 _25307) : (term86 _25307 fn) = (term86 _25307 fn).
Proof. exact (eq_refl (term86 _25307 fn)). Qed.
Lemma lem1100335 {_25307 : Type'} (fn : type1131 _25307) : (term87 _25307 fn) = (term64 _25307 fn).
Proof. exact (MK_COMB (@lem1100334 _25307 fn) (@lem1100333 _25307 fn)). Qed.
Lemma lem1100336 {_25307 : Type'} : (term88 _25307) = (term89 _25307).
Proof. exact (fun_ext (fun fn : type1131 _25307 => @lem1100335 _25307 fn)). Qed.
Lemma lem1100337 {_25307 : Type'} : (@ex ((list _25307) -> (_25307 -> Prop) -> Prop)) = (@ex ((list _25307) -> (_25307 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((list _25307) -> (_25307 -> Prop) -> Prop))). Qed.
Lemma lem1100338 {_25307 : Type'} : (term70 _25307) = (term90 _25307).
Proof. exact (MK_COMB (@lem1100337 _25307) (@lem1100336 _25307)). Qed.
Lemma lem1100339 {_25307 : Type'} : term90 _25307.
Proof. exact (EQ_MP (@lem1100338 _25307) (@lem1100316 _25307)). Qed.
Lemma lem1100340 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term64 _25307 _17969.
Proof. exact (h1). Qed.
Lemma lem1100341 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term57 _25307 _17969.
Proof. exact (proj2 (@lem1100340 _25307 _17969 h1)). Qed.
Lemma lem1100342 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : (_17969 (@nil _25307)) = (term55 _25307).
Proof. exact (proj1 (@lem1100340 _25307 _17969 h1)). Qed.
Lemma lem1100343 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term64 _25307 _17969.
Proof. exact (conj (@lem1100342 _25307 _17969 h1) (@lem1100341 _25307 _17969 h1)). Qed.
Lemma lem1100344 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term90 _25307.
Proof. exact (ex_intro (term89 _25307) _17969 (@lem1100343 _25307 _17969 h1)). Qed.
Lemma lem1100345 {_25307 : Type'} (h1 : term90 _25307) : term90 _25307.
Proof. exact (h1). Qed.
Lemma lem1100346 {_25307 : Type'} (h1 : term90 _25307) : term90 _25307.
Proof. exact (ex_elim (@lem1100345 _25307 h1) (fun _17969 : type1131 _25307 => fun h0 : term89 _25307 _17969 => @lem1100344 _25307 _17969 h0)). Qed.
Lemma lem1100347 {_25307 : Type'} : (term90 _25307) = (term90 _25307).
Proof. exact (prop_ext (fun h1 : term90 _25307 => @lem1100346 _25307 h1) (fun h1 : term90 _25307 => @lem1100339 _25307)). Qed.
Lemma lem1100348 {_25307 : Type'} : term90 _25307.
Proof. exact (EQ_MP (@lem1100347 _25307) (@lem1100339 _25307)). Qed.
Lemma lem1100349 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term64 _25307 _17969) : term91 _25307.
Proof. exact (ex_intro (term92 _25307) _17969 (@lem1100308 _25307 _17969 h1)). Qed.
Lemma lem1100350 {_25307 : Type'} (h1 : term90 _25307) : term90 _25307.
Proof. exact (h1). Qed.
Lemma lem1100351 {_25307 : Type'} (h1 : term90 _25307) : term91 _25307.
Proof. exact (ex_elim (@lem1100350 _25307 h1) (fun _17969 : type1131 _25307 => fun h0 : term89 _25307 _17969 => @lem1100349 _25307 _17969 h0)). Qed.
Lemma lem1100352 {_25307 : Type'} : (term90 _25307) = (term91 _25307).
Proof. exact (prop_ext (fun h1 : term90 _25307 => @lem1100351 _25307 h1) (fun h1 : term91 _25307 => @lem1100348 _25307)). Qed.
Lemma lem1100353 {_25307 : Type'} : term91 _25307.
Proof. exact (EQ_MP (@lem1100352 _25307) (@lem1100348 _25307)). Qed.
Lemma lem1100354 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term54 _25307 _17969) : term54 _25307 _17969.
Proof. exact (h1). Qed.
Lemma lem1100355 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : ALL' = (term4 _25307 _17969)) : (term54 _25307 _17969) = (term53 _25307 ALL').
Proof. exact (SYM (@lem1100276 _25307 ALL' _17969 h1)). Qed.
Lemma lem1100356 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : term54 _25307 _17969) (h2 : ALL' = (term4 _25307 _17969)) : term53 _25307 ALL'.
Proof. exact (EQ_MP (@lem1100355 _25307 ALL' _17969 h2) (@lem1100354 _25307 _17969 h1)). Qed.
Lemma lem1100357 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : term54 _25307 _17969) (h2 : ALL' = (term4 _25307 _17969)) : term93 _25307.
Proof. exact (ex_intro (term94 _25307) ALL' (@lem1100356 _25307 ALL' _17969 h1 h2)). Qed.
Lemma lem1100358 {_25307 : Type'} (_17969 : type1131 _25307) : (term4 _25307 _17969) = (term4 _25307 _17969).
Proof. exact (eq_refl (term4 _25307 _17969)). Qed.
Lemma lem1100359 {_25307 : Type'} (ALL' : type663 _25307) (_17969 : type1131 _25307) (h1 : term54 _25307 _17969) : term95 _25307 ALL' _17969.
Proof. exact (fun h0 : ALL' = (term4 _25307 _17969) => @lem1100357 _25307 ALL' _17969 h1 h0). Qed.
Lemma lem1100360 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term54 _25307 _17969) : term96 _25307 _17969.
Proof. exact (@lem1100359 _25307 (term4 _25307 _17969) _17969 h1). Qed.
Lemma lem1100361 {_25307 : Type'} (_17969 : type1131 _25307) (h1 : term54 _25307 _17969) : term93 _25307.
Proof. exact (@lem1100360 _25307 _17969 h1 (@lem1100358 _25307 _17969)). Qed.
Lemma lem1100362 {_25307 : Type'} (h1 : term91 _25307) : term91 _25307.
Proof. exact (h1). Qed.
Lemma lem1100363 {_25307 : Type'} (h1 : term91 _25307) : term93 _25307.
Proof. exact (ex_elim (@lem1100362 _25307 h1) (fun _17969 : type1131 _25307 => fun h0 : term92 _25307 _17969 => @lem1100361 _25307 _17969 h0)). Qed.
Lemma lem1100364 {_25307 : Type'} : (term91 _25307) = (term93 _25307).
Proof. exact (prop_ext (fun h1 : term91 _25307 => @lem1100363 _25307 h1) (fun h1 : term93 _25307 => @lem1100353 _25307)). Qed.
Lemma lem1100365 {_25307 : Type'} : term93 _25307.
Proof. exact (EQ_MP (@lem1100364 _25307) (@lem1100353 _25307)). Qed.
Lemma lem1100366 {_25307 : Type'} : term97 _25307.
Proof. exact (fun _17973 : type1674 => @lem1100365 _25307). Qed.
Lemma lem1100367 {A B : Type'} (P : type1413 A B) : term98 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1100368 {A B : Type'} (P : type1413 A B) : (term98 A B P) = ((term99 A B P) = (term100 A B P)).
Proof. exact (eq_refl (term98 A B P)). Qed.
Lemma lem1100371 {A B : Type'} (P : type1413 A B) : (term99 A B P) = (term100 A B P).
Proof. exact (EQ_MP (@lem1100368 A B P) (@lem1100367 A B P)). Qed.
Lemma lem1100372 {_25307 : Type'} (P : type1294 _25307) : (term101 _25307 P) = (term102 _25307 P).
Proof. exact (@lem1100371 type1674 (type663 _25307) P). Qed.
Lemma lem1100373 {_25307 : Type'} : (term103 _25307) = (term104 _25307).
Proof. exact (@lem1100372 _25307 (term105 _25307)). Qed.
Lemma lem1100374 {_25307 : Type'} (_17973 : type1674) : (term106 _25307 _17973) = (term94 _25307).
Proof. exact (eq_refl (term106 _25307 _17973)). Qed.
Lemma lem1100375 {_25307 : Type'} (ALL' : type663 _25307) : ALL' = ALL'.
Proof. exact (eq_refl ALL'). Qed.
Lemma lem1100376 {_25307 : Type'} (_17973 : type1674) (ALL' : type663 _25307) : (term107 _25307 _17973 ALL') = (term108 _25307 ALL').
Proof. exact (MK_COMB (@lem1100374 _25307 _17973) (@lem1100375 _25307 ALL')). Qed.
Lemma lem1100377 {_25307 : Type'} (ALL' : type663 _25307) : (term108 _25307 ALL') = (term53 _25307 ALL').
Proof. exact (eq_refl (term108 _25307 ALL')). Qed.
Lemma lem1100378 {_25307 : Type'} (_17973 : type1674) (ALL' : type663 _25307) : (term107 _25307 _17973 ALL') = (term53 _25307 ALL').
Proof. exact (TRANS (@lem1100376 _25307 _17973 ALL') (@lem1100377 _25307 ALL')). Qed.
Lemma lem1100379 {_25307 : Type'} (_17973 : type1674) : (term109 _25307 _17973) = (term94 _25307).
Proof. exact (fun_ext (fun ALL' : type663 _25307 => @lem1100378 _25307 _17973 ALL')). Qed.
Lemma lem1100380 {_25307 : Type'} : (@ex ((_25307 -> Prop) -> (list _25307) -> Prop)) = (@ex ((_25307 -> Prop) -> (list _25307) -> Prop)).
Proof. exact (eq_refl (@ex ((_25307 -> Prop) -> (list _25307) -> Prop))). Qed.
Lemma lem1100381 {_25307 : Type'} (_17973 : type1674) : (term110 _25307 _17973) = (term93 _25307).
Proof. exact (MK_COMB (@lem1100380 _25307) (@lem1100379 _25307 _17973)). Qed.
Lemma lem1100382 {_25307 : Type'} : (term111 _25307) = (term112 _25307).
Proof. exact (fun_ext (fun _17973 : type1674 => @lem1100381 _25307 _17973)). Qed.
Lemma lem1100383 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem1100384 {_25307 : Type'} : (term103 _25307) = (term97 _25307).
Proof. exact (MK_COMB (@lem1100383) (@lem1100382 _25307)). Qed.
Lemma lem1100385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1100386 {_25307 : Type'} : (term113 _25307) = (term114 _25307).
Proof. exact (MK_COMB (@lem1100385) (@lem1100384 _25307)). Qed.
Lemma lem1100387 {_25307 : Type'} (_17973 : type1674) : (term106 _25307 _17973) = (term94 _25307).
Proof. exact (eq_refl (term106 _25307 _17973)). Qed.
Lemma lem1100388 {_25307 : Type'} (ALL' : type1298 _25307) (_17973 : type1674) : (ALL' _17973) = (ALL' _17973).
Proof. exact (eq_refl (ALL' _17973)). Qed.
Lemma lem1100389 {_25307 : Type'} (ALL' : type1298 _25307) (_17973 : type1674) : (term115 _25307 ALL' _17973) = (term116 _25307 ALL' _17973).
Proof. exact (MK_COMB (@lem1100387 _25307 _17973) (@lem1100388 _25307 ALL' _17973)). Qed.
Lemma lem1100390 {_25307 : Type'} (ALL' : type1298 _25307) (_17973 : type1674) : (term116 _25307 ALL' _17973) = (term117 _25307 ALL' _17973).
Proof. exact (eq_refl (term116 _25307 ALL' _17973)). Qed.
Lemma lem1100391 {_25307 : Type'} (ALL' : type1298 _25307) (_17973 : type1674) : (term115 _25307 ALL' _17973) = (term117 _25307 ALL' _17973).
Proof. exact (TRANS (@lem1100389 _25307 ALL' _17973) (@lem1100390 _25307 ALL' _17973)). Qed.
Lemma lem1100392 {_25307 : Type'} (ALL' : type1298 _25307) : (term118 _25307 ALL') = (term119 _25307 ALL').
Proof. exact (fun_ext (fun _17973 : type1674 => @lem1100391 _25307 ALL' _17973)). Qed.
Lemma lem1100393 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem1100394 {_25307 : Type'} (ALL' : type1298 _25307) : (term120 _25307 ALL') = (term121 _25307 ALL').
Proof. exact (MK_COMB (@lem1100393) (@lem1100392 _25307 ALL')). Qed.
Lemma lem1100395 {_25307 : Type'} : (term122 _25307) = (term123 _25307).
Proof. exact (fun_ext (fun ALL' : type1298 _25307 => @lem1100394 _25307 ALL')). Qed.
Lemma lem1100396 {_25307 : Type'} : (@ex ((prod nat (prod nat nat)) -> (_25307 -> Prop) -> (list _25307) -> Prop)) = (@ex ((prod nat (prod nat nat)) -> (_25307 -> Prop) -> (list _25307) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> (_25307 -> Prop) -> (list _25307) -> Prop))). Qed.
Lemma lem1100397 {_25307 : Type'} : (term104 _25307) = (term124 _25307).
Proof. exact (MK_COMB (@lem1100396 _25307) (@lem1100395 _25307)). Qed.
Lemma lem1100398 {_25307 : Type'} : ((term103 _25307) = (term104 _25307)) = ((term97 _25307) = (term124 _25307)).
Proof. exact (MK_COMB (@lem1100386 _25307) (@lem1100397 _25307)). Qed.
Lemma lem1100399 {_25307 : Type'} : (term97 _25307) = (term124 _25307).
Proof. exact (EQ_MP (@lem1100398 _25307) (@lem1100373 _25307)). Qed.
Lemma lem1100400 {_25307 : Type'} : term124 _25307.
Proof. exact (EQ_MP (@lem1100399 _25307) (@lem1100366 _25307)). Qed.
Lemma lem1100402 {A : Type'} : (@ex A) = (term125 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1100403 {_25307 : Type'} : (@ex ((prod nat (prod nat nat)) -> (_25307 -> Prop) -> (list _25307) -> Prop)) = (term126 _25307).
Proof. exact (@lem1100402 (type1298 _25307)). Qed.
Lemma lem1100404 {_25307 : Type'} : (term123 _25307) = (term123 _25307).
Proof. exact (eq_refl (term123 _25307)). Qed.
Lemma lem1100405 {_25307 : Type'} : (term124 _25307) = (term127 _25307).
Proof. exact (MK_COMB (@lem1100403 _25307) (@lem1100404 _25307)). Qed.
Lemma lem1100406 {_25307 : Type'} : (term127 _25307) = (term128 _25307).
Proof. exact (eq_refl (term127 _25307)). Qed.
Lemma lem1100407 {_25307 : Type'} : (term124 _25307) = (term128 _25307).
Proof. exact (TRANS (@lem1100405 _25307) (@lem1100406 _25307)). Qed.
Lemma lem1100408 {_25307 : Type'} : term128 _25307.
Proof. exact (EQ_MP (@lem1100407 _25307) (@lem1100400 _25307)). Qed.
