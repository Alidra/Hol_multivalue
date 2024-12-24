Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_IDEMPOT_term_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_COMPLEMENT_spec.
Require Import ARBITRARY_UNION_OF_IDEMPOT_spec.
Require Import COMPL_COMPL_spec.
Require Import ETA_AX_spec.
Require Import FUN_EQ_THM_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4868152 {A : Type'} (P : type686 A) : term0 A P.
Proof. exact (@lem4868151 A P). Qed.
Lemma lem4868153 {A : Type'} (P : type686 A) : (term0 A P) = ((term1 A P) = (@UNION_OF A (@ARBITRARY A) P)).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4868157 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term2 A B f g)) : (f = g) = (term2 A B f g).
Proof. exact (h1). Qed.
Lemma lem4868158 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term2 A B f g)) : (term2 A B f g) = (f = g).
Proof. exact (SYM (@lem4868157 A B f g h1)). Qed.
Lemma lem4868159 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term2 A B f g) = (f = g)) : (term2 A B f g) = (f = g).
Proof. exact (h1). Qed.
Lemma lem4868160 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term2 A B f g) = (f = g)) : (f = g) = (term2 A B f g).
Proof. exact (SYM (@lem4868159 A B f g h1)). Qed.
Lemma lem4868161 {A B : Type'} (f : A -> B) (g : A -> B) : ((f = g) = (term2 A B f g)) = ((term2 A B f g) = (f = g)).
Proof. exact (prop_ext (fun h1 : (f = g) = (term2 A B f g) => @lem4868158 A B f g h1) (fun h1 : (term2 A B f g) = (f = g) => @lem4868160 A B f g h1)). Qed.
Lemma lem4868162 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (fun_ext (fun g : A -> B => @lem4868161 A B f g)). Qed.
Lemma lem4868163 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4868164 {A B : Type'} (f : A -> B) : (term5 A B f) = (term6 A B f).
Proof. exact (MK_COMB (@lem4868163 A B) (@lem4868162 A B f)). Qed.
Lemma lem4868165 {A B : Type'} : (term7 A B) = (term8 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4868164 A B f)). Qed.
Lemma lem4868166 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4868167 {A B : Type'} : (term9 A B) = (term10 A B).
Proof. exact (MK_COMB (@lem4868166 A B) (@lem4868165 A B)). Qed.
Lemma lem4868168 {A B : Type'} : term10 A B.
Proof. exact (EQ_MP (@lem4868167 A B) (@lem9220 A B)). Qed.
Lemma lem4868169 {A B : Type'} (t : A -> B) : term11 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem4868170 {A B : Type'} (t : A -> B) : (term11 A B t) = ((term12 A B t) = t).
Proof. exact (eq_refl (term11 A B t)). Qed.
Lemma lem4868171 {A B : Type'} (t : A -> B) : (term12 A B t) = t.
Proof. exact (EQ_MP (@lem4868170 A B t) (@lem4868169 A B t)). Qed.
Lemma lem4868172 {A B : Type'} (f : A -> B) : term13 A B f.
Proof. exact (@lem4868168 A B f). Qed.
Lemma lem4868173 {A B : Type'} (f : A -> B) : (term13 A B f) = (term6 A B f).
Proof. exact (eq_refl (term13 A B f)). Qed.
Lemma lem4868174 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (EQ_MP (@lem4868173 A B f) (@lem4868172 A B f)). Qed.
Lemma lem4868175 {A B : Type'} (f : A -> B) (g : A -> B) : term14 A B f g.
Proof. exact (@lem4868174 A B f g). Qed.
Lemma lem4868176 {A B : Type'} (f : A -> B) (g : A -> B) : (term14 A B f g) = ((term2 A B f g) = (f = g)).
Proof. exact (eq_refl (term14 A B f g)). Qed.
Lemma lem4868183 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = (f = g).
Proof. exact (EQ_MP (@lem4868176 A B f g) (@lem4868175 A B f g)). Qed.
Lemma lem4868184 {A : Type'} (f : type686 A) (g : type686 A) : (term15 A f g) = (f = g).
Proof. exact (@lem4868183 (A -> Prop) Prop f g). Qed.
Lemma lem4868185 {A : Type'} (P : type686 A) : (term16 A P) = ((term17 A P) = (term18 A P)).
Proof. exact (@lem4868184 A (term17 A P) (term18 A P)). Qed.
Lemma lem4868186 {A : Type'} (P : type686 A) (s : A -> Prop) : (term19 A P s) = (@INTERSECTION_OF A (@ARBITRARY A) P s).
Proof. exact (eq_refl (term19 A P s)). Qed.
Lemma lem4868187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868188 {A : Type'} (P : type686 A) (s : A -> Prop) : (term20 A P s) = (term21 A P s).
Proof. exact (MK_COMB (@lem4868187) (@lem4868186 A P s)). Qed.
Lemma lem4868189 {A : Type'} (P : type686 A) (s : A -> Prop) : (term22 A P s) = (term23 A P s).
Proof. exact (eq_refl (term22 A P s)). Qed.
Lemma lem4868190 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term19 A P s) = (term22 A P s)) = ((@INTERSECTION_OF A (@ARBITRARY A) P s) = (term23 A P s)).
Proof. exact (MK_COMB (@lem4868188 A P s) (@lem4868189 A P s)). Qed.
Lemma lem4868191 {A : Type'} (P : type686 A) : (term24 A P) = (term25 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4868190 A P s)). Qed.
Lemma lem4868192 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4868193 {A : Type'} (P : type686 A) : (term16 A P) = (term26 A P).
Proof. exact (MK_COMB (@lem4868192 A) (@lem4868191 A P)). Qed.
Lemma lem4868194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868195 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (MK_COMB (@lem4868194) (@lem4868193 A P)). Qed.
Lemma lem4868196 {A : Type'} (P : type686 A) : ((term17 A P) = (term18 A P)) = ((term17 A P) = (term18 A P)).
Proof. exact (eq_refl ((term17 A P) = (term18 A P))). Qed.
Lemma lem4868197 {A : Type'} (P : type686 A) : ((term16 A P) = ((term17 A P) = (term18 A P))) = ((term26 A P) = ((term17 A P) = (term18 A P))).
Proof. exact (MK_COMB (@lem4868195 A P) (@lem4868196 A P)). Qed.
Lemma lem4868198 {A : Type'} (P : type686 A) : (term26 A P) = ((term17 A P) = (term18 A P)).
Proof. exact (EQ_MP (@lem4868197 A P) (@lem4868185 A P)). Qed.
Lemma lem4868201 {A : Type'} (t : type686 A) : (term29 A t) = t.
Proof. exact (@lem4868171 (A -> Prop) Prop t). Qed.
Lemma lem4868202 {A : Type'} (P : type686 A) : (term17 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P).
Proof. exact (@lem4868201 A (@INTERSECTION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4868203 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4868204 {A : Type'} (P : type686 A) : (term30 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4868203 A) (@lem4868202 A P)). Qed.
Lemma lem4868205 {A : Type'} (P : type686 A) : (term18 A P) = (term18 A P).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem4868206 {A : Type'} (P : type686 A) : ((term17 A P) = (term18 A P)) = ((@INTERSECTION_OF A (@ARBITRARY A) P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4868204 A P) (@lem4868205 A P)). Qed.
Lemma lem4868209 {A : Type'} (P : type686 A) : (term26 A P) = ((@INTERSECTION_OF A (@ARBITRARY A) P) = (term18 A P)).
Proof. exact (TRANS (@lem4868198 A P) (@lem4868206 A P)). Qed.
Lemma lem4868210 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4868209 A P)). Qed.
Lemma lem4868211 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4868212 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (MK_COMB (@lem4868211 A) (@lem4868210 A)). Qed.
Lemma lem4868214 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = (f = g).
Proof. exact (EQ_MP (@lem4868176 A B f g) (@lem4868175 A B f g)). Qed.
Lemma lem4868215 {A : Type'} (f : type174 A) (g : type174 A) : (term36 A f g) = (f = g).
Proof. exact (@lem4868214 (type686 A) (type686 A) f g). Qed.
Lemma lem4868216 {A : Type'} : (term37 A) = ((term38 A) = (term39 A)).
Proof. exact (@lem4868215 A (term38 A) (term39 A)). Qed.
Lemma lem4868217 {A : Type'} (P : type686 A) : (term40 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P).
Proof. exact (eq_refl (term40 A P)). Qed.
Lemma lem4868218 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4868219 {A : Type'} (P : type686 A) : (term41 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4868218 A) (@lem4868217 A P)). Qed.
Lemma lem4868220 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4868221 {A : Type'} (P : type686 A) : ((term40 A P) = (term42 A P)) = ((@INTERSECTION_OF A (@ARBITRARY A) P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4868219 A P) (@lem4868220 A P)). Qed.
Lemma lem4868222 {A : Type'} : (term43 A) = (term33 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4868221 A P)). Qed.
Lemma lem4868223 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4868224 {A : Type'} : (term37 A) = (term35 A).
Proof. exact (MK_COMB (@lem4868223 A) (@lem4868222 A)). Qed.
Lemma lem4868225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868226 {A : Type'} : (term44 A) = (term45 A).
Proof. exact (MK_COMB (@lem4868225) (@lem4868224 A)). Qed.
Lemma lem4868227 {A : Type'} : ((term38 A) = (term39 A)) = ((term38 A) = (term39 A)).
Proof. exact (eq_refl ((term38 A) = (term39 A))). Qed.
Lemma lem4868228 {A : Type'} : ((term37 A) = ((term38 A) = (term39 A))) = ((term35 A) = ((term38 A) = (term39 A))).
Proof. exact (MK_COMB (@lem4868226 A) (@lem4868227 A)). Qed.
Lemma lem4868229 {A : Type'} : (term35 A) = ((term38 A) = (term39 A)).
Proof. exact (EQ_MP (@lem4868228 A) (@lem4868216 A)). Qed.
Lemma lem4868232 {A : Type'} (t : type174 A) : (term46 A t) = t.
Proof. exact (@lem4868171 (type686 A) (type686 A) t). Qed.
Lemma lem4868233 {A : Type'} : (term38 A) = (@INTERSECTION_OF A (@ARBITRARY A)).
Proof. exact (@lem4868232 A (@INTERSECTION_OF A (@ARBITRARY A))). Qed.
Lemma lem4868234 {A : Type'} : (@eq (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop)) = (@eq (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4868235 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (MK_COMB (@lem4868234 A) (@lem4868233 A)). Qed.
Lemma lem4868236 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (eq_refl (term39 A)). Qed.
Lemma lem4868237 {A : Type'} : ((term38 A) = (term39 A)) = ((@INTERSECTION_OF A (@ARBITRARY A)) = (term39 A)).
Proof. exact (MK_COMB (@lem4868235 A) (@lem4868236 A)). Qed.
Lemma lem4868240 {A : Type'} : (term35 A) = ((@INTERSECTION_OF A (@ARBITRARY A)) = (term39 A)).
Proof. exact (TRANS (@lem4868229 A) (@lem4868237 A)). Qed.
Lemma lem4868241 {A : Type'} : (term34 A) = ((@INTERSECTION_OF A (@ARBITRARY A)) = (term39 A)).
Proof. exact (TRANS (@lem4868212 A) (@lem4868240 A)). Qed.
Lemma lem4868243 {A B : Type'} (t : A -> B) : term11 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem4868244 {A B : Type'} (t : A -> B) : (term11 A B t) = ((term12 A B t) = t).
Proof. exact (eq_refl (term11 A B t)). Qed.
Lemma lem4868245 {A B : Type'} (t : A -> B) : (term12 A B t) = t.
Proof. exact (EQ_MP (@lem4868244 A B t) (@lem4868243 A B t)). Qed.
Lemma lem4868246 {A : Type'} (s : A -> Prop) : term49 A s.
Proof. exact (@lem3270825 A s). Qed.
Lemma lem4868247 {A : Type'} (s : A -> Prop) : (term49 A s) = ((term50 A s) = s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem4868256 {A : Type'} : (@INTERSECTION_OF A (@ARBITRARY A)) = (term39 A).
Proof. exact (EQ_MP (@lem4868241 A) (@lem4860962 A)). Qed.
Lemma lem4868258 {A : Type'} : (@INTERSECTION_OF A (@ARBITRARY A)) = (term39 A).
Proof. exact (EQ_MP (@lem4868241 A) (@lem4860962 A)). Qed.
Lemma lem4868259 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4868260 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term42 A P).
Proof. exact (MK_COMB (@lem4868258 A) (@lem4868259 A P)). Qed.
Lemma lem4868262 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4868263 {A : Type'} (f : type174 A) (y : type686 A) : (term52 A f y) = (f y).
Proof. exact (@lem4868262 (type686 A) (type686 A) f y). Qed.
Lemma lem4868264 {A : Type'} (P : type686 A) : (term53 A P) = (term42 A P).
Proof. exact (@lem4868263 A (term39 A) P). Qed.
Lemma lem4868265 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4868266 {A : Type'} : (term54 A) = (term39 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4868265 A P)). Qed.
Lemma lem4868267 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4868268 {A : Type'} (P : type686 A) : (term53 A P) = (term42 A P).
Proof. exact (MK_COMB (@lem4868266 A) (@lem4868267 A P)). Qed.
Lemma lem4868269 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4868270 {A : Type'} (P : type686 A) : (term55 A P) = (term56 A P).
Proof. exact (MK_COMB (@lem4868269 A) (@lem4868268 A P)). Qed.
Lemma lem4868271 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4868272 {A : Type'} (P : type686 A) : ((term53 A P) = (term42 A P)) = ((term42 A P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4868270 A P) (@lem4868271 A P)). Qed.
Lemma lem4868273 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (EQ_MP (@lem4868272 A P) (@lem4868264 A P)). Qed.
Lemma lem4868274 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term18 A P).
Proof. exact (TRANS (@lem4868260 A P) (@lem4868273 A P)). Qed.
Lemma lem4868275 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (MK_COMB (@lem4868256 A) (@lem4868274 A P)). Qed.
Lemma lem4868277 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4868278 {A : Type'} (f : type174 A) (y : type686 A) : (term52 A f y) = (f y).
Proof. exact (@lem4868277 (type686 A) (type686 A) f y). Qed.
Lemma lem4868279 {A : Type'} (P : type686 A) : (term59 A P) = (term58 A P).
Proof. exact (@lem4868278 A (term39 A) (term18 A P)). Qed.
Lemma lem4868280 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4868281 {A : Type'} : (term54 A) = (term39 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4868280 A P)). Qed.
Lemma lem4868282 {A : Type'} (P : type686 A) : (term18 A P) = (term18 A P).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem4868283 {A : Type'} (P : type686 A) : (term59 A P) = (term58 A P).
Proof. exact (MK_COMB (@lem4868281 A) (@lem4868282 A P)). Qed.
Lemma lem4868284 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4868285 {A : Type'} (P : type686 A) : (term60 A P) = (term61 A P).
Proof. exact (MK_COMB (@lem4868284 A) (@lem4868283 A P)). Qed.
Lemma lem4868286 {A : Type'} (P : type686 A) : (term58 A P) = (term62 A P).
Proof. exact (eq_refl (term58 A P)). Qed.
Lemma lem4868287 {A : Type'} (P : type686 A) : ((term59 A P) = (term58 A P)) = ((term58 A P) = (term62 A P)).
Proof. exact (MK_COMB (@lem4868285 A P) (@lem4868286 A P)). Qed.
Lemma lem4868288 {A : Type'} (P : type686 A) : (term58 A P) = (term62 A P).
Proof. exact (EQ_MP (@lem4868287 A P) (@lem4868279 A P)). Qed.
Lemma lem4868290 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4868291 {A : Type'} (f : type686 A) (y : A -> Prop) : (term63 A f y) = (f y).
Proof. exact (@lem4868290 (A -> Prop) Prop f y). Qed.
Lemma lem4868292 {A : Type'} (P : type686 A) (s : A -> Prop) : (term64 A P s) = (term65 A P s).
Proof. exact (@lem4868291 A (term18 A P) (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4868293 {A : Type'} (P : type686 A) (s : A -> Prop) : (term22 A P s) = (term23 A P s).
Proof. exact (eq_refl (term22 A P s)). Qed.
Lemma lem4868294 {A : Type'} (P : type686 A) : (term66 A P) = (term18 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4868293 A P s)). Qed.
Lemma lem4868295 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4868296 {A : Type'} (P : type686 A) (s : A -> Prop) : (term64 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4868294 A P) (@lem4868295 A s)). Qed.
Lemma lem4868297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868298 {A : Type'} (P : type686 A) (s : A -> Prop) : (term67 A P s) = (term68 A P s).
Proof. exact (MK_COMB (@lem4868297) (@lem4868296 A P s)). Qed.
Lemma lem4868299 {A : Type'} (P : type686 A) (s : A -> Prop) : (term65 A P s) = (term69 A P s).
Proof. exact (eq_refl (term65 A P s)). Qed.
Lemma lem4868300 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term64 A P s) = (term65 A P s)) = ((term65 A P s) = (term69 A P s)).
Proof. exact (MK_COMB (@lem4868298 A P s) (@lem4868299 A P s)). Qed.
Lemma lem4868301 {A : Type'} (P : type686 A) (s : A -> Prop) : (term65 A P s) = (term69 A P s).
Proof. exact (EQ_MP (@lem4868300 A P s) (@lem4868292 A P s)). Qed.
Lemma lem4868303 {A : Type'} (s : A -> Prop) : (term50 A s) = s.
Proof. exact (EQ_MP (@lem4868247 A s) (@lem4868246 A s)). Qed.
Lemma lem4868304 {A : Type'} (s : A -> Prop) : (term50 A s) = s.
Proof. exact (@lem4868303 A s). Qed.
Lemma lem4868305 {A : Type'} (P : type686 A) : (term70 A P) = (term70 A P).
Proof. exact (eq_refl (term70 A P)). Qed.
Lemma lem4868306 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term71 A P s).
Proof. exact (MK_COMB (@lem4868305 A P) (@lem4868304 A s)). Qed.
Lemma lem4868307 {A : Type'} (P : type686 A) (s : A -> Prop) : (term65 A P s) = (term71 A P s).
Proof. exact (TRANS (@lem4868301 A P s) (@lem4868306 A P s)). Qed.
Lemma lem4868308 {A : Type'} (P : type686 A) : (term72 A P) = (term73 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4868307 A P s)). Qed.
Lemma lem4868309 {A : Type'} (t : type686 A) : (term29 A t) = t.
Proof. exact (@lem4868245 (A -> Prop) Prop t). Qed.
Lemma lem4868310 {A : Type'} (P : type686 A) : (term73 A P) = (term70 A P).
Proof. exact (@lem4868309 A (term70 A P)). Qed.
Lemma lem4868311 {A : Type'} (P : type686 A) : (term72 A P) = (term70 A P).
Proof. exact (TRANS (@lem4868308 A P) (@lem4868310 A P)). Qed.
Lemma lem4868312 {A : Type'} : (@UNION_OF A (@ARBITRARY A)) = (@UNION_OF A (@ARBITRARY A)).
Proof. exact (eq_refl (@UNION_OF A (@ARBITRARY A))). Qed.
Lemma lem4868313 {A : Type'} (P : type686 A) : (term74 A P) = (term75 A P).
Proof. exact (MK_COMB (@lem4868312 A) (@lem4868311 A P)). Qed.
Lemma lem4868314 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4868315 {A : Type'} (P : type686 A) (s : A -> Prop) : (term76 A P s) = (term77 A P s).
Proof. exact (MK_COMB (@lem4868313 A P) (@lem4868314 A s)). Qed.
Lemma lem4868316 {A : Type'} (P : type686 A) : (term62 A P) = (term78 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4868315 A P s)). Qed.
Lemma lem4868317 {A : Type'} (P : type686 A) : (term58 A P) = (term78 A P).
Proof. exact (TRANS (@lem4868288 A P) (@lem4868316 A P)). Qed.
Lemma lem4868318 {A : Type'} (P : type686 A) : (term57 A P) = (term78 A P).
Proof. exact (TRANS (@lem4868275 A P) (@lem4868317 A P)). Qed.
Lemma lem4868319 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4868320 {A : Type'} (P : type686 A) : (term79 A P) = (term80 A P).
Proof. exact (MK_COMB (@lem4868319 A) (@lem4868318 A P)). Qed.
Lemma lem4868322 {A : Type'} : (@INTERSECTION_OF A (@ARBITRARY A)) = (term39 A).
Proof. exact (EQ_MP (@lem4868241 A) (@lem4860962 A)). Qed.
Lemma lem4868323 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4868324 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term42 A P).
Proof. exact (MK_COMB (@lem4868322 A) (@lem4868323 A P)). Qed.
Lemma lem4868326 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4868327 {A : Type'} (f : type174 A) (y : type686 A) : (term52 A f y) = (f y).
Proof. exact (@lem4868326 (type686 A) (type686 A) f y). Qed.
Lemma lem4868328 {A : Type'} (P : type686 A) : (term53 A P) = (term42 A P).
Proof. exact (@lem4868327 A (term39 A) P). Qed.
Lemma lem4868329 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4868330 {A : Type'} : (term54 A) = (term39 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4868329 A P)). Qed.
Lemma lem4868331 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4868332 {A : Type'} (P : type686 A) : (term53 A P) = (term42 A P).
Proof. exact (MK_COMB (@lem4868330 A) (@lem4868331 A P)). Qed.
Lemma lem4868333 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4868334 {A : Type'} (P : type686 A) : (term55 A P) = (term56 A P).
Proof. exact (MK_COMB (@lem4868333 A) (@lem4868332 A P)). Qed.
Lemma lem4868335 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4868336 {A : Type'} (P : type686 A) : ((term53 A P) = (term42 A P)) = ((term42 A P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4868334 A P) (@lem4868335 A P)). Qed.
Lemma lem4868337 {A : Type'} (P : type686 A) : (term42 A P) = (term18 A P).
Proof. exact (EQ_MP (@lem4868336 A P) (@lem4868328 A P)). Qed.
Lemma lem4868338 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term18 A P).
Proof. exact (TRANS (@lem4868324 A P) (@lem4868337 A P)). Qed.
Lemma lem4868339 {A : Type'} (P : type686 A) : ((term57 A P) = (@INTERSECTION_OF A (@ARBITRARY A) P)) = ((term78 A P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4868320 A P) (@lem4868338 A P)). Qed.
Lemma lem4868342 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4868339 A P)). Qed.
Lemma lem4868343 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4868344 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (MK_COMB (@lem4868343 A) (@lem4868342 A)). Qed.
Lemma lem4868349 {A : Type'} : (term84 A) = (term83 A).
Proof. exact (SYM (@lem4868344 A)). Qed.
Lemma lem4868357 {A : Type'} (P : type686 A) : (term1 A P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (EQ_MP (@lem4868153 A P) (@lem4868152 A P)). Qed.
Lemma lem4868358 {A : Type'} (P : type686 A) : (term1 A P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (@lem4868357 A P). Qed.
Lemma lem4868359 {A : Type'} (P : type686 A) : (term75 A P) = (term70 A P).
Proof. exact (@lem4868358 A (term85 A P)). Qed.
Lemma lem4868360 {A : Type'} (s : A -> Prop) : (@DIFF A (@UNIV A) s) = (@DIFF A (@UNIV A) s).
Proof. exact (eq_refl (@DIFF A (@UNIV A) s)). Qed.
Lemma lem4868361 {A : Type'} (P : type686 A) (s : A -> Prop) : (term77 A P s) = (term23 A P s).
Proof. exact (MK_COMB (@lem4868359 A P) (@lem4868360 A s)). Qed.
Lemma lem4868362 {A : Type'} (P : type686 A) : (term78 A P) = (term18 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4868361 A P s)). Qed.
Lemma lem4868363 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4868364 {A : Type'} (P : type686 A) : (term80 A P) = (term86 A P).
Proof. exact (MK_COMB (@lem4868363 A) (@lem4868362 A P)). Qed.
Lemma lem4868365 {A : Type'} (P : type686 A) : (term18 A P) = (term18 A P).
Proof. exact (eq_refl (term18 A P)). Qed.
Lemma lem4868366 {A : Type'} (P : type686 A) : ((term78 A P) = (term18 A P)) = ((term18 A P) = (term18 A P)).
Proof. exact (MK_COMB (@lem4868364 A P) (@lem4868365 A P)). Qed.
Lemma lem4868368 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4868369 {A : Type'} (x : type686 A) : (x = x) = True.
Proof. exact (@lem4868368 (type686 A) x). Qed.
Lemma lem4868370 {A : Type'} (P : type686 A) : ((term18 A P) = (term18 A P)) = True.
Proof. exact (@lem4868369 A (term18 A P)). Qed.
Lemma lem4868371 {A : Type'} (P : type686 A) : ((term78 A P) = (term18 A P)) = True.
Proof. exact (TRANS (@lem4868366 A P) (@lem4868370 A P)). Qed.
Lemma lem4868372 {A : Type'} : (term82 A) = (term87 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4868371 A P)). Qed.
Lemma lem4868373 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4868374 {A : Type'} : (term84 A) = (term88 A).
Proof. exact (MK_COMB (@lem4868373 A) (@lem4868372 A)). Qed.
Lemma lem4868376 {A : Type'} (t : Prop) : (term89 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4868377 {A : Type'} (t : Prop) : (term90 A t) = t.
Proof. exact (@lem4868376 (type686 A) t). Qed.
Lemma lem4868378 {A : Type'} : (term88 A) = True.
Proof. exact (@lem4868377 A True). Qed.
Lemma lem4868379 {A : Type'} : (term84 A) = True.
Proof. exact (TRANS (@lem4868374 A) (@lem4868378 A)). Qed.
Lemma lem4868380 {A : Type'} : True = (term84 A).
Proof. exact (SYM (@lem4868379 A)). Qed.
Lemma lem4868381 {A : Type'} : term84 A.
Proof. exact (EQ_MP (@lem4868380 A) (@lem0)). Qed.
Lemma lem4868382 {A : Type'} : term83 A.
Proof. exact (EQ_MP (@lem4868349 A) (@lem4868381 A)). Qed.
