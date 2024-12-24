Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_FILTER_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm1106562_spec.
Require Import thm1106563_spec.
Require Import thm1106571_spec.
Require Import thm1106572_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem1148190 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1148191 {_27073 : Type'} (P : type1143 _27073) : term0 _27073 P.
Proof. exact (@lem1148190 _27073 P). Qed.
Lemma lem1148192 {_27073 : Type'} (P : _27073 -> Prop) : term1 _27073 P.
Proof. exact (@lem1148191 _27073 (term2 _27073 P)). Qed.
Lemma lem1148193 {_27073 : Type'} (P : _27073 -> Prop) : (term3 _27073 P) = (term4 _27073 P).
Proof. exact (eq_refl (term3 _27073 P)). Qed.
Lemma lem1148194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1148195 {_27073 : Type'} (P : _27073 -> Prop) : (term5 _27073 P) = (term6 _27073 P).
Proof. exact (MK_COMB (@lem1148194) (@lem1148193 _27073 P)). Qed.
Lemma lem1148196 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term7 _27073 P t) = (term8 _27073 P t).
Proof. exact (eq_refl (term7 _27073 P t)). Qed.
Lemma lem1148197 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1148198 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term9 _27073 P t) = (term10 _27073 P t).
Proof. exact (MK_COMB (@lem1148197) (@lem1148196 _27073 P t)). Qed.
Lemma lem1148199 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (t : list _27073) : (term11 _27073 P h t) = (term12 _27073 P h t).
Proof. exact (eq_refl (term11 _27073 P h t)). Qed.
Lemma lem1148200 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (t : list _27073) : (term13 _27073 P h t) = (term14 _27073 P h t).
Proof. exact (MK_COMB (@lem1148198 _27073 P t) (@lem1148199 _27073 P h t)). Qed.
Lemma lem1148201 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term15 _27073 P h) = (term16 _27073 P h).
Proof. exact (fun_ext (fun t : list _27073 => @lem1148200 _27073 P h t)). Qed.
Lemma lem1148202 {_27073 : Type'} : (@all (list _27073)) = (@all (list _27073)).
Proof. exact (eq_refl (@all (list _27073))). Qed.
Lemma lem1148203 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term17 _27073 P h) = (term18 _27073 P h).
Proof. exact (MK_COMB (@lem1148202 _27073) (@lem1148201 _27073 P h)). Qed.
Lemma lem1148204 {_27073 : Type'} (P : _27073 -> Prop) : (term19 _27073 P) = (term20 _27073 P).
Proof. exact (fun_ext (fun h : _27073 => @lem1148203 _27073 P h)). Qed.
Lemma lem1148205 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1148206 {_27073 : Type'} (P : _27073 -> Prop) : (term21 _27073 P) = (term22 _27073 P).
Proof. exact (MK_COMB (@lem1148205 _27073) (@lem1148204 _27073 P)). Qed.
Lemma lem1148207 {_27073 : Type'} (P : _27073 -> Prop) : (term23 _27073 P) = (term24 _27073 P).
Proof. exact (MK_COMB (@lem1148195 _27073 P) (@lem1148206 _27073 P)). Qed.
Lemma lem1148208 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1148209 {_27073 : Type'} (P : _27073 -> Prop) : (term25 _27073 P) = (term26 _27073 P).
Proof. exact (MK_COMB (@lem1148208) (@lem1148207 _27073 P)). Qed.
Lemma lem1148210 {_27073 : Type'} (P : _27073 -> Prop) (l : list _27073) : (term7 _27073 P l) = (term8 _27073 P l).
Proof. exact (eq_refl (term7 _27073 P l)). Qed.
Lemma lem1148211 {_27073 : Type'} (P : _27073 -> Prop) : (term27 _27073 P) = (term2 _27073 P).
Proof. exact (fun_ext (fun l : list _27073 => @lem1148210 _27073 P l)). Qed.
Lemma lem1148212 {_27073 : Type'} : (@all (list _27073)) = (@all (list _27073)).
Proof. exact (eq_refl (@all (list _27073))). Qed.
Lemma lem1148213 {_27073 : Type'} (P : _27073 -> Prop) : (term28 _27073 P) = (term29 _27073 P).
Proof. exact (MK_COMB (@lem1148212 _27073) (@lem1148211 _27073 P)). Qed.
Lemma lem1148214 {_27073 : Type'} (P : _27073 -> Prop) : (term1 _27073 P) = (term30 _27073 P).
Proof. exact (MK_COMB (@lem1148209 _27073 P) (@lem1148213 _27073 P)). Qed.
Lemma lem1148215 {_27073 : Type'} (P : _27073 -> Prop) : term30 _27073 P.
Proof. exact (EQ_MP (@lem1148214 _27073 P) (@lem1148192 _27073 P)). Qed.
Lemma lem1148216 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term8 _27073 P t.
Proof. exact (h1). Qed.
Lemma lem1148228 {_25594 : Type'} (P : _25594 -> Prop) : (@FILTER _25594 P (@nil _25594)) = (@nil _25594).
Proof. exact (EQ_MP (@lem1106563 _25594 P) (@lem1106562 _25594 P)). Qed.
Lemma lem1148229 {_27073 : Type'} (P : _27073 -> Prop) : (@FILTER _27073 P (@nil _27073)) = (@nil _27073).
Proof. exact (@lem1148228 _27073 P). Qed.
Lemma lem1148230 {_27073 : Type'} (x : _27073) : (@List.In _27073 x) = (@List.In _27073 x).
Proof. exact (eq_refl (@List.In _27073 x)). Qed.
Lemma lem1148231 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term31 _27073 x P) = (@List.In _27073 x (@nil _27073)).
Proof. exact (MK_COMB (@lem1148230 _27073 x) (@lem1148229 _27073 P)). Qed.
Lemma lem1148233 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1148234 {_27073 : Type'} (x : _27073) : (@List.In _27073 x (@nil _27073)) = False.
Proof. exact (@lem1148233 _27073 x). Qed.
Lemma lem1148235 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) : (term31 _27073 x P) = False.
Proof. exact (TRANS (@lem1148231 _27073 P x) (@lem1148234 _27073 x)). Qed.
Lemma lem1148236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1148237 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) : (term32 _27073 x P) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1148236) (@lem1148235 _27073 x P)). Qed.
Lemma lem1148241 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1148242 {_27073 : Type'} (x : _27073) : (@List.In _27073 x (@nil _27073)) = False.
Proof. exact (@lem1148241 _27073 x). Qed.
Lemma lem1148243 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term33 _27073 P x) = (term33 _27073 P x).
Proof. exact (eq_refl (term33 _27073 P x)). Qed.
Lemma lem1148244 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term34 _27073 P x) = (term35 _27073 P x).
Proof. exact (MK_COMB (@lem1148243 _27073 P x) (@lem1148242 _27073 x)). Qed.
Lemma lem1148246 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1148247 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term35 _27073 P x) = False.
Proof. exact (@lem1148246 (P x)). Qed.
Lemma lem1148248 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term34 _27073 P x) = False.
Proof. exact (TRANS (@lem1148244 _27073 P x) (@lem1148247 _27073 P x)). Qed.
Lemma lem1148249 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : ((term31 _27073 x P) = (term34 _27073 P x)) = (False = False).
Proof. exact (MK_COMB (@lem1148237 _27073 x P) (@lem1148248 _27073 P x)). Qed.
Lemma lem1148251 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1148252 : (False = False) = (~ False).
Proof. exact (@lem1148251 False). Qed.
Lemma lem1148254 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1148255 : (False = False) = True.
Proof. exact (TRANS (@lem1148252) (@lem1148254)). Qed.
Lemma lem1148256 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : ((term31 _27073 x P) = (term34 _27073 P x)) = True.
Proof. exact (TRANS (@lem1148249 _27073 P x) (@lem1148255)). Qed.
Lemma lem1148257 {_27073 : Type'} (P : _27073 -> Prop) : (term36 _27073 P) = (term37 _27073).
Proof. exact (fun_ext (fun x : _27073 => @lem1148256 _27073 P x)). Qed.
Lemma lem1148258 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1148259 {_27073 : Type'} (P : _27073 -> Prop) : (term4 _27073 P) = (term38 _27073).
Proof. exact (MK_COMB (@lem1148258 _27073) (@lem1148257 _27073 P)). Qed.
Lemma lem1148261 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1148262 {_27073 : Type'} (t : Prop) : (term39 _27073 t) = t.
Proof. exact (@lem1148261 _27073 t). Qed.
Lemma lem1148263 {_27073 : Type'} : (term38 _27073) = True.
Proof. exact (@lem1148262 _27073 True). Qed.
Lemma lem1148264 {_27073 : Type'} (P : _27073 -> Prop) : (term4 _27073 P) = True.
Proof. exact (TRANS (@lem1148259 _27073 P) (@lem1148263 _27073)). Qed.
Lemma lem1148265 {_27073 : Type'} (P : _27073 -> Prop) : True = (term4 _27073 P).
Proof. exact (SYM (@lem1148264 _27073 P)). Qed.
Lemma lem1148266 {_27073 : Type'} (P : _27073 -> Prop) : term4 _27073 P.
Proof. exact (EQ_MP (@lem1148265 _27073 P) (@lem0)). Qed.
Lemma lem1148281 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term40 _25594 P h t) = (term41 _25594 h P t).
Proof. exact (EQ_MP (@lem1106572 _25594 h P t) (@lem1106571 _25594 h P t)). Qed.
Lemma lem1148282 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (t : list _27073) : (term40 _27073 P h t) = (term41 _27073 h P t).
Proof. exact (@lem1148281 _27073 h P t). Qed.
Lemma lem1148283 {_27073 : Type'} (x : _27073) : (@List.In _27073 x) = (@List.In _27073 x).
Proof. exact (eq_refl (@List.In _27073 x)). Qed.
Lemma lem1148284 {_27073 : Type'} (x : _27073) (h : _27073) (P : _27073 -> Prop) (t : list _27073) : (term42 _27073 x P h t) = (term43 _27073 x h P t).
Proof. exact (MK_COMB (@lem1148283 _27073 x) (@lem1148282 _27073 h P t)). Qed.
Lemma lem1148285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1148286 {_27073 : Type'} (x : _27073) (h : _27073) (P : _27073 -> Prop) (t : list _27073) : (term44 _27073 x P h t) = (term45 _27073 x h P t).
Proof. exact (MK_COMB (@lem1148285) (@lem1148284 _27073 x h P t)). Qed.
Lemma lem1148290 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term46 _25376 x h t) = (term47 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1148291 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term46 _27073 x h t) = (term47 _27073 h x t).
Proof. exact (@lem1148290 _27073 h x t). Qed.
Lemma lem1148296 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term33 _27073 P x) = (term33 _27073 P x).
Proof. exact (eq_refl (term33 _27073 P x)). Qed.
Lemma lem1148297 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term48 _27073 P x h t) = (term49 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148296 _27073 P x) (@lem1148291 _27073 h x t)). Qed.
Lemma lem1148300 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : ((term42 _27073 x P h t) = (term48 _27073 P x h t)) = ((term43 _27073 x h P t) = (term49 _27073 P h x t)).
Proof. exact (MK_COMB (@lem1148286 _27073 x h P t) (@lem1148297 _27073 P h x t)). Qed.
Lemma lem1148303 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (t : list _27073) : (term50 _27073 P h t) = (term51 _27073 P h t).
Proof. exact (fun_ext (fun x : _27073 => @lem1148300 _27073 P h x t)). Qed.
Lemma lem1148304 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1148305 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (t : list _27073) : (term12 _27073 P h t) = (term52 _27073 P h t).
Proof. exact (MK_COMB (@lem1148304 _27073) (@lem1148303 _27073 P h t)). Qed.
Lemma lem1148310 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (t : list _27073) : (term52 _27073 P h t) = (term12 _27073 P h t).
Proof. exact (SYM (@lem1148305 _27073 P h t)). Qed.
Lemma lem1148311 {_27073 : Type'} (_474 : list _27073) (_475 : Prop) (_476 : type1143 _27073) (_477 : list _27073) : (term53 _27073 _476 _475 _474 _477) = (term54 _27073 _474 _475 _476 _477).
Proof. exact (@lem13473 (list _27073) _474 _475 _476 _477). Qed.
Lemma lem1148312 {_27073 : Type'} (_474 : list _27073) (_475 : Prop) (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (_477 : list _27073) : (term55 _27073 P h x t _475 _474 _477) = (term56 _27073 _474 _475 P h x t _477).
Proof. exact (@lem1148311 _27073 _474 _475 (term57 _27073 P h x t) _477). Qed.
Lemma lem1148313 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) : (term58 _27073 x h P t) = (term59 _27073 h x P t).
Proof. exact (@lem1148312 _27073 (term60 _27073 h P t) (P h) P h x t (@FILTER _27073 P t)). Qed.
Lemma lem1148314 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term61 _27073 h x P t) = ((term62 _27073 x P t) = (term49 _27073 P h x t)).
Proof. exact (eq_refl (term61 _27073 h x P t)). Qed.
Lemma lem1148315 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term63 _27073 P h) = (term63 _27073 P h).
Proof. exact (eq_refl (term63 _27073 P h)). Qed.
Lemma lem1148316 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term64 _27073 h x P t) = (term65 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148315 _27073 P h) (@lem1148314 _27073 P h x t)). Qed.
Lemma lem1148317 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term66 _27073 x h P t) = ((term67 _27073 x h P t) = (term49 _27073 P h x t)).
Proof. exact (eq_refl (term66 _27073 x h P t)). Qed.
Lemma lem1148318 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term68 _27073 P h) = (term68 _27073 P h).
Proof. exact (eq_refl (term68 _27073 P h)). Qed.
Lemma lem1148319 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term69 _27073 x h P t) = (term70 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148318 _27073 P h) (@lem1148317 _27073 P h x t)). Qed.
Lemma lem1148320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1148321 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term71 _27073 x h P t) = (term72 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148320) (@lem1148319 _27073 P h x t)). Qed.
Lemma lem1148322 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term59 _27073 h x P t) = (term73 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148321 _27073 P h x t) (@lem1148316 _27073 P h x t)). Qed.
Lemma lem1148323 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term58 _27073 x h P t) = ((term43 _27073 x h P t) = (term49 _27073 P h x t)).
Proof. exact (eq_refl (term58 _27073 x h P t)). Qed.
Lemma lem1148324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1148325 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term74 _27073 x h P t) = (term75 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148324) (@lem1148323 _27073 P h x t)). Qed.
Lemma lem1148326 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : ((term58 _27073 x h P t) = (term59 _27073 h x P t)) = (((term43 _27073 x h P t) = (term49 _27073 P h x t)) = (term73 _27073 P h x t)).
Proof. exact (MK_COMB (@lem1148325 _27073 P h x t) (@lem1148322 _27073 P h x t)). Qed.
Lemma lem1148327 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : ((term43 _27073 x h P t) = (term49 _27073 P h x t)) = (term73 _27073 P h x t).
Proof. exact (EQ_MP (@lem1148326 _27073 P h x t) (@lem1148313 _27073 h x P t)). Qed.
Lemma lem1148328 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term73 _27073 P h x t) = ((term43 _27073 x h P t) = (term49 _27073 P h x t)).
Proof. exact (SYM (@lem1148327 _27073 P h x t)). Qed.
Lemma lem1148329 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (h1 : P h) : P h.
Proof. exact (h1). Qed.
Lemma lem1148346 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (h1 : term76 _27073 P h) : term76 _27073 P h.
Proof. exact (h1). Qed.
Lemma lem1148365 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term77 _27073 P t x.
Proof. exact (@lem1148216 _27073 P t h1 x). Qed.
Lemma lem1148366 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term77 _27073 P t x) = ((term62 _27073 x P t) = (term78 _27073 P x t)).
Proof. exact (eq_refl (term77 _27073 P t x)). Qed.
Lemma lem1148373 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term46 _25376 x h t) = (term47 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1148374 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term46 _27073 x h t) = (term47 _27073 h x t).
Proof. exact (@lem1148373 _27073 h x t). Qed.
Lemma lem1148375 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) : (term67 _27073 x h P t) = (term79 _27073 h x P t).
Proof. exact (@lem1148374 _27073 h x (@FILTER _27073 P t)). Qed.
Lemma lem1148381 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : (term62 _27073 x P t) = (term78 _27073 P x t).
Proof. exact (EQ_MP (@lem1148366 _27073 P x t) (@lem1148365 _27073 x P t h1)). Qed.
Lemma lem1148382 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : (term62 _27073 x P t) = (term78 _27073 P x t).
Proof. exact (@lem1148381 _27073 x P t h1). Qed.
Lemma lem1148385 {_27073 : Type'} (x : _27073) (h : _27073) : (term80 _27073 x h) = (term80 _27073 x h).
Proof. exact (eq_refl (term80 _27073 x h)). Qed.
Lemma lem1148386 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : (term79 _27073 h x P t) = (term81 _27073 h P x t).
Proof. exact (MK_COMB (@lem1148385 _27073 x h) (@lem1148382 _27073 x P t h1)). Qed.
Lemma lem1148389 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : (term67 _27073 x h P t) = (term81 _27073 h P x t).
Proof. exact (TRANS (@lem1148375 _27073 h x P t) (@lem1148386 _27073 h x P t h1)). Qed.
Lemma lem1148390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1148391 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : (term82 _27073 x h P t) = (term83 _27073 h P x t).
Proof. exact (MK_COMB (@lem1148390) (@lem1148389 _27073 h x P t h1)). Qed.
Lemma lem1148398 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term49 _27073 P h x t) = (term49 _27073 P h x t).
Proof. exact (eq_refl (term49 _27073 P h x t)). Qed.
Lemma lem1148399 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : ((term67 _27073 x h P t) = (term49 _27073 P h x t)) = ((term81 _27073 h P x t) = (term49 _27073 P h x t)).
Proof. exact (MK_COMB (@lem1148391 _27073 h x P t h1) (@lem1148398 _27073 P h x t)). Qed.
Lemma lem1148402 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : ((term81 _27073 h P x t) = (term49 _27073 P h x t)) = ((term67 _27073 x h P t) = (term49 _27073 P h x t)).
Proof. exact (SYM (@lem1148399 _27073 h x P t h1)). Qed.
Lemma lem1148405 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term77 _27073 P t x.
Proof. exact (@lem1148216 _27073 P t h1 x). Qed.
Lemma lem1148406 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term77 _27073 P t x) = ((term62 _27073 x P t) = (term78 _27073 P x t)).
Proof. exact (eq_refl (term77 _27073 P t x)). Qed.
Lemma lem1148413 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : (term62 _27073 x P t) = (term78 _27073 P x t).
Proof. exact (EQ_MP (@lem1148406 _27073 P x t) (@lem1148405 _27073 x P t h1)). Qed.
Lemma lem1148414 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : (term62 _27073 x P t) = (term78 _27073 P x t).
Proof. exact (@lem1148413 _27073 x P t h1). Qed.
Lemma lem1148417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1148418 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : (term84 _27073 x P t) = (term85 _27073 P x t).
Proof. exact (MK_COMB (@lem1148417) (@lem1148414 _27073 x P t h1)). Qed.
Lemma lem1148425 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term49 _27073 P h x t) = (term49 _27073 P h x t).
Proof. exact (eq_refl (term49 _27073 P h x t)). Qed.
Lemma lem1148426 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : ((term62 _27073 x P t) = (term49 _27073 P h x t)) = ((term78 _27073 P x t) = (term49 _27073 P h x t)).
Proof. exact (MK_COMB (@lem1148418 _27073 x P t h1) (@lem1148425 _27073 P h x t)). Qed.
Lemma lem1148429 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : ((term78 _27073 P x t) = (term49 _27073 P h x t)) = ((term62 _27073 x P t) = (term49 _27073 P h x t)).
Proof. exact (SYM (@lem1148426 _27073 h x P t h1)). Qed.
Lemma lem1148431 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1148432 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : ((term81 _27073 h P x t) = (term49 _27073 P h x t)) = (term87 _27073 P h x t).
Proof. exact (@lem1148431 ((term81 _27073 h P x t) = (term49 _27073 P h x t))). Qed.
Lemma lem1148433 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term87 _27073 P h x t) = ((term81 _27073 h P x t) = (term49 _27073 P h x t)).
Proof. exact (SYM (@lem1148432 _27073 P h x t)). Qed.
Lemma lem1148434 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term88 _27073 P h x t) : term88 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1148437 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term89 _27073 P h x t) : term89 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1148438 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term90 _27073 P h x t.
Proof. exact (fun h0 : term89 _27073 P h x t => @lem1148437 _27073 P h x t h0). Qed.
Lemma lem1148439 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term90 _27073 P h x t) : term90 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1148440 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term89 _27073 P h x t) : term89 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1148441 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term89 _27073 P h x t) (h2 : term90 _27073 P h x t) : term89 _27073 P h x t.
Proof. exact (@lem1148439 _27073 P h x t h2 (@lem1148440 _27073 P h x t h1)). Qed.
Lemma lem1148442 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term89 _27073 P h x t) : term91 _27073 P h x t.
Proof. exact (fun h0 : term90 _27073 P h x t => @lem1148441 _27073 P h x t h1 h0). Qed.
Lemma lem1148443 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term90 _27073 P h x t) : term90 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1148444 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term89 _27073 P h x t) (h2 : term90 _27073 P h x t) : term89 _27073 P h x t.
Proof. exact (@lem1148442 _27073 P h x t h1 (@lem1148443 _27073 P h x t h2)). Qed.
Lemma lem1148445 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term90 _27073 P h x t) : term90 _27073 P h x t.
Proof. exact (fun h0 : term89 _27073 P h x t => @lem1148444 _27073 P h x t h0 h1). Qed.
Lemma lem1148446 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term92 _27073 P h x t.
Proof. exact (fun h0 : term90 _27073 P h x t => @lem1148445 _27073 P h x t h0). Qed.
Lemma lem1148449 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term90 _27073 P h x t.
Proof. exact (@lem1148446 _27073 P h x t (@lem1148438 _27073 P h x t)). Qed.
Lemma lem1148450 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term90 _27073 P h x t.
Proof. exact (@lem1148449 _27073 P h x t). Qed.
Lemma lem1148478 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1148479 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term87 _27073 P h x t) = (term93 _27073 P h x t).
Proof. exact (@lem1148478 (term88 _27073 P h x t)). Qed.
Lemma lem1148481 (t : Prop) : (term94 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1148482 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term93 _27073 P h x t) = ((term81 _27073 h P x t) = (term49 _27073 P h x t)).
Proof. exact (@lem1148481 ((term81 _27073 h P x t) = (term49 _27073 P h x t))). Qed.
Lemma lem1148483 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term87 _27073 P h x t) = ((term81 _27073 h P x t) = (term49 _27073 P h x t)).
Proof. exact (TRANS (@lem1148479 _27073 P h x t) (@lem1148482 _27073 P h x t)). Qed.
Lemma lem1148492 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term68 _27073 P h) = (term68 _27073 P h).
Proof. exact (eq_refl (term68 _27073 P h)). Qed.
Lemma lem1148493 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term95 _27073 P h x t) = (term96 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148492 _27073 P h) (@lem1148483 _27073 P h x t)). Qed.
Lemma lem1148496 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term10 _27073 P t) = (term10 _27073 P t).
Proof. exact (eq_refl (term10 _27073 P t)). Qed.
Lemma lem1148497 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term89 _27073 P h x t) = (term97 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148496 _27073 P t) (@lem1148493 _27073 P h x t)). Qed.
Lemma lem1148500 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term98 _27073 h x t) = (term99 _27073 h x t).
Proof. exact (fun_ext (fun P : _27073 -> Prop => @lem1148497 _27073 P h x t)). Qed.
Lemma lem1148501 {_27073 : Type'} : (@all (_27073 -> Prop)) = (@all (_27073 -> Prop)).
Proof. exact (eq_refl (@all (_27073 -> Prop))). Qed.
Lemma lem1148502 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term100 _27073 h x t) = (term101 _27073 h x t).
Proof. exact (MK_COMB (@lem1148501 _27073) (@lem1148500 _27073 h x t)). Qed.
Lemma lem1148507 {_27073 : Type'} (x : _27073) (t : list _27073) : (term102 _27073 x t) = (term103 _27073 x t).
Proof. exact (fun_ext (fun h : _27073 => @lem1148502 _27073 h x t)). Qed.
Lemma lem1148508 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1148509 {_27073 : Type'} (x : _27073) (t : list _27073) : (term104 _27073 x t) = (term105 _27073 x t).
Proof. exact (MK_COMB (@lem1148508 _27073) (@lem1148507 _27073 x t)). Qed.
Lemma lem1148514 {_27073 : Type'} (t : list _27073) : (term106 _27073 t) = (term107 _27073 t).
Proof. exact (fun_ext (fun x : _27073 => @lem1148509 _27073 x t)). Qed.
Lemma lem1148515 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1148516 {_27073 : Type'} (t : list _27073) : (term108 _27073 t) = (term109 _27073 t).
Proof. exact (MK_COMB (@lem1148515 _27073) (@lem1148514 _27073 t)). Qed.
Lemma lem1148521 {_27073 : Type'} : (term110 _27073) = (term111 _27073).
Proof. exact (fun_ext (fun t : list _27073 => @lem1148516 _27073 t)). Qed.
Lemma lem1148522 {_27073 : Type'} : (@all (list _27073)) = (@all (list _27073)).
Proof. exact (eq_refl (@all (list _27073))). Qed.
Lemma lem1148531 {_27073 : Type'} : (term112 _27073) = (term113 _27073).
Proof. exact (MK_COMB (@lem1148522 _27073) (@lem1148521 _27073)). Qed.
Lemma lem1148556 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term96 _27073 P h x t) = (term96 _27073 P h x t).
Proof. exact (eq_refl (term96 _27073 P h x t)). Qed.
Lemma lem1148565 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : ((term62 _27073 x P t) = (term78 _27073 P x t)) = ((term62 _27073 x P t) = (term78 _27073 P x t)).
Proof. exact (eq_refl ((term62 _27073 x P t) = (term78 _27073 P x t))). Qed.
Lemma lem1148566 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term114 _27073 P t) = (term114 _27073 P t).
Proof. exact (fun_ext (fun x : _27073 => @lem1148565 _27073 P x t)). Qed.
Lemma lem1148567 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1148568 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term8 _27073 P t) = (term8 _27073 P t).
Proof. exact (MK_COMB (@lem1148567 _27073) (@lem1148566 _27073 P t)). Qed.
Lemma lem1148569 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1148570 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term10 _27073 P t) = (term10 _27073 P t).
Proof. exact (MK_COMB (@lem1148569) (@lem1148568 _27073 P t)). Qed.
Lemma lem1148571 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term97 _27073 P h x t) = (term97 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148570 _27073 P t) (@lem1148556 _27073 P h x t)). Qed.
Lemma lem1148572 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term99 _27073 h x t) = (term99 _27073 h x t).
Proof. exact (fun_ext (fun P : _27073 -> Prop => @lem1148571 _27073 P h x t)). Qed.
Lemma lem1148573 {_27073 : Type'} : (@all (_27073 -> Prop)) = (@all (_27073 -> Prop)).
Proof. exact (eq_refl (@all (_27073 -> Prop))). Qed.
Lemma lem1148574 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term101 _27073 h x t) = (term101 _27073 h x t).
Proof. exact (MK_COMB (@lem1148573 _27073) (@lem1148572 _27073 h x t)). Qed.
Lemma lem1148575 {_27073 : Type'} (x : _27073) (t : list _27073) : (term103 _27073 x t) = (term103 _27073 x t).
Proof. exact (fun_ext (fun h : _27073 => @lem1148574 _27073 h x t)). Qed.
Lemma lem1148576 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1148577 {_27073 : Type'} (x : _27073) (t : list _27073) : (term105 _27073 x t) = (term105 _27073 x t).
Proof. exact (MK_COMB (@lem1148576 _27073) (@lem1148575 _27073 x t)). Qed.
Lemma lem1148578 {_27073 : Type'} (t : list _27073) : (term107 _27073 t) = (term107 _27073 t).
Proof. exact (fun_ext (fun x : _27073 => @lem1148577 _27073 x t)). Qed.
Lemma lem1148579 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1148580 {_27073 : Type'} (t : list _27073) : (term109 _27073 t) = (term109 _27073 t).
Proof. exact (MK_COMB (@lem1148579 _27073) (@lem1148578 _27073 t)). Qed.
Lemma lem1148581 {_27073 : Type'} : (term111 _27073) = (term111 _27073).
Proof. exact (fun_ext (fun t : list _27073 => @lem1148580 _27073 t)). Qed.
Lemma lem1148582 {_27073 : Type'} : (@all (list _27073)) = (@all (list _27073)).
Proof. exact (eq_refl (@all (list _27073))). Qed.
Lemma lem1148583 {_27073 : Type'} : (term113 _27073) = (term113 _27073).
Proof. exact (MK_COMB (@lem1148582 _27073) (@lem1148581 _27073)). Qed.
Lemma lem1148630 {_27073 : Type'} : (term112 _27073) = (term113 _27073).
Proof. exact (TRANS (@lem1148531 _27073) (@lem1148583 _27073)). Qed.
Lemma lem1148631 {_27073 : Type'} : (term113 _27073) = (term112 _27073).
Proof. exact (SYM (@lem1148630 _27073)). Qed.
Lemma lem1148635 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1148636 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : ((term81 _27073 h P x t) = (term49 _27073 P h x t)) = (term87 _27073 P h x t).
Proof. exact (@lem1148635 ((term81 _27073 h P x t) = (term49 _27073 P h x t))). Qed.
Lemma lem1148637 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term87 _27073 P h x t) = ((term81 _27073 h P x t) = (term49 _27073 P h x t)).
Proof. exact (SYM (@lem1148636 _27073 P h x t)). Qed.
Lemma lem1148638 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term88 _27073 P h x t) : term88 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1148799 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (h1 : P h) : P h.
Proof. exact (h1). Qed.
Lemma lem1148810 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term115 _27073 P x t) = (term116 _27073 P x t).
Proof. exact (@lem17045 (P x) (@List.In _27073 x t)). Qed.
Lemma lem1148815 {_27073 : Type'} (x : _27073) (h : _27073) : (term117 _27073 x h) = (term117 _27073 x h).
Proof. exact (eq_refl (term117 _27073 x h)). Qed.
Lemma lem1148816 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term118 _27073 h P x t) = (term119 _27073 h P x t).
Proof. exact (MK_COMB (@lem1148815 _27073 x h) (@lem1148810 _27073 P x t)). Qed.
Lemma lem1148817 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term120 _27073 h P x t) = (term118 _27073 h P x t).
Proof. exact (@lem17160 (x = h) (term78 _27073 P x t)). Qed.
Lemma lem1148818 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term120 _27073 h P x t) = (term119 _27073 h P x t).
Proof. exact (TRANS (@lem1148817 _27073 h P x t) (@lem1148816 _27073 h P x t)). Qed.
Lemma lem1148832 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term121 _27073 h x t) = (term122 _27073 h x t).
Proof. exact (@lem17160 (x = h) (@List.In _27073 x t)). Qed.
Lemma lem1148837 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term123 _27073 P x) = (term123 _27073 P x).
Proof. exact (eq_refl (term123 _27073 P x)). Qed.
Lemma lem1148838 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term124 _27073 P h x t) = (term125 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148837 _27073 P x) (@lem1148832 _27073 h x t)). Qed.
Lemma lem1148839 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term126 _27073 P h x t) = (term124 _27073 P h x t).
Proof. exact (@lem17045 (P x) (term47 _27073 h x t)). Qed.
Lemma lem1148840 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term126 _27073 P h x t) = (term125 _27073 P h x t).
Proof. exact (TRANS (@lem1148839 _27073 P h x t) (@lem1148838 _27073 P h x t)). Qed.
Lemma lem1148843 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term49 _27073 P h x t) = (term49 _27073 P h x t).
Proof. exact (eq_refl (term49 _27073 P h x t)). Qed.
Lemma lem1148844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1148845 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term127 _27073 h P x t) = (term128 _27073 h P x t).
Proof. exact (MK_COMB (@lem1148844) (@lem1148818 _27073 h P x t)). Qed.
Lemma lem1148846 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term129 _27073 P h x t) = (term130 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148845 _27073 h P x t) (@lem1148843 _27073 P h x t)). Qed.
Lemma lem1148848 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term131 _27073 h P x t) = (term131 _27073 h P x t).
Proof. exact (eq_refl (term131 _27073 h P x t)). Qed.
Lemma lem1148849 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term132 _27073 P h x t) = (term133 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148848 _27073 h P x t) (@lem1148840 _27073 P h x t)). Qed.
Lemma lem1148850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1148851 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term134 _27073 P h x t) = (term135 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148850) (@lem1148849 _27073 P h x t)). Qed.
Lemma lem1148852 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term136 _27073 P h x t) = (term137 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148851 _27073 P h x t) (@lem1148846 _27073 P h x t)). Qed.
Lemma lem1148853 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term88 _27073 P h x t) = (term136 _27073 P h x t).
Proof. exact (@lem17646 (term81 _27073 h P x t) (term49 _27073 P h x t)). Qed.
Lemma lem1148858 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term88 _27073 P h x t) = (term137 _27073 P h x t).
Proof. exact (TRANS (@lem1148853 _27073 P h x t) (@lem1148852 _27073 P h x t)). Qed.
Lemma lem1148859 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term88 _27073 P h x t) : term137 _27073 P h x t.
Proof. exact (EQ_MP (@lem1148858 _27073 P h x t) (@lem1148638 _27073 P h x t h1)). Qed.
Lemma lem1148936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1148937 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1148936 _27073 Prop f x). Qed.
Lemma lem1148939 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (P h) = (@I (_27073 -> Prop) P h).
Proof. exact (@lem1148937 _27073 P h). Qed.
Lemma lem1148953 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term47 _27073 h x t) = (term47 _27073 h x t).
Proof. exact (eq_refl (term47 _27073 h x t)). Qed.
Lemma lem1148958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1148959 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1148958 _27073 Prop f x). Qed.
Lemma lem1148961 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1148959 _27073 P x). Qed.
Lemma lem1148962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1148963 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term33 _27073 P x) = (term138 _27073 P x).
Proof. exact (MK_COMB (@lem1148962) (@lem1148961 _27073 P x)). Qed.
Lemma lem1148964 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term49 _27073 P h x t) = (term139 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148963 _27073 P x) (@lem1148953 _27073 h x t)). Qed.
Lemma lem1148971 {_27073 : Type'} (x : _27073) (t : list _27073) : (term140 _27073 x t) = (term140 _27073 x t).
Proof. exact (eq_refl (term140 _27073 x t)). Qed.
Lemma lem1148972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1148977 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1148978 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1148977 _27073 Prop f x). Qed.
Lemma lem1148980 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1148978 _27073 P x). Qed.
Lemma lem1148981 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term76 _27073 P x) = (term141 _27073 P x).
Proof. exact (MK_COMB (@lem1148972) (@lem1148980 _27073 P x)). Qed.
Lemma lem1148982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1148983 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term123 _27073 P x) = (term142 _27073 P x).
Proof. exact (MK_COMB (@lem1148982) (@lem1148981 _27073 P x)). Qed.
Lemma lem1148984 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term116 _27073 P x t) = (term143 _27073 P x t).
Proof. exact (MK_COMB (@lem1148983 _27073 P x) (@lem1148971 _27073 x t)). Qed.
Lemma lem1148993 {_27073 : Type'} (x : _27073) (h : _27073) : (term117 _27073 x h) = (term117 _27073 x h).
Proof. exact (eq_refl (term117 _27073 x h)). Qed.
Lemma lem1148994 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term119 _27073 h P x t) = (term144 _27073 h P x t).
Proof. exact (MK_COMB (@lem1148993 _27073 x h) (@lem1148984 _27073 P x t)). Qed.
Lemma lem1148995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1148996 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term128 _27073 h P x t) = (term145 _27073 h P x t).
Proof. exact (MK_COMB (@lem1148995) (@lem1148994 _27073 h P x t)). Qed.
Lemma lem1148997 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term130 _27073 P h x t) = (term146 _27073 P h x t).
Proof. exact (MK_COMB (@lem1148996 _27073 h P x t) (@lem1148964 _27073 P h x t)). Qed.
Lemma lem1149014 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term122 _27073 h x t) = (term122 _27073 h x t).
Proof. exact (eq_refl (term122 _27073 h x t)). Qed.
Lemma lem1149015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1149020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1149021 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1149020 _27073 Prop f x). Qed.
Lemma lem1149023 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1149021 _27073 P x). Qed.
Lemma lem1149024 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term76 _27073 P x) = (term141 _27073 P x).
Proof. exact (MK_COMB (@lem1149015) (@lem1149023 _27073 P x)). Qed.
Lemma lem1149025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1149026 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term123 _27073 P x) = (term142 _27073 P x).
Proof. exact (MK_COMB (@lem1149025) (@lem1149024 _27073 P x)). Qed.
Lemma lem1149027 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term125 _27073 P h x t) = (term147 _27073 P h x t).
Proof. exact (MK_COMB (@lem1149026 _27073 P x) (@lem1149014 _27073 h x t)). Qed.
Lemma lem1149032 {_27073 : Type'} (x : _27073) (t : list _27073) : (@List.In _27073 x t) = (@List.In _27073 x t).
Proof. exact (eq_refl (@List.In _27073 x t)). Qed.
Lemma lem1149037 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1149038 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1149037 _27073 Prop f x). Qed.
Lemma lem1149040 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1149038 _27073 P x). Qed.
Lemma lem1149041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1149042 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term33 _27073 P x) = (term138 _27073 P x).
Proof. exact (MK_COMB (@lem1149041) (@lem1149040 _27073 P x)). Qed.
Lemma lem1149043 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term78 _27073 P x t) = (term148 _27073 P x t).
Proof. exact (MK_COMB (@lem1149042 _27073 P x) (@lem1149032 _27073 x t)). Qed.
Lemma lem1149050 {_27073 : Type'} (x : _27073) (h : _27073) : (term80 _27073 x h) = (term80 _27073 x h).
Proof. exact (eq_refl (term80 _27073 x h)). Qed.
Lemma lem1149051 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term81 _27073 h P x t) = (term149 _27073 h P x t).
Proof. exact (MK_COMB (@lem1149050 _27073 x h) (@lem1149043 _27073 P x t)). Qed.
Lemma lem1149052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1149053 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term131 _27073 h P x t) = (term150 _27073 h P x t).
Proof. exact (MK_COMB (@lem1149052) (@lem1149051 _27073 h P x t)). Qed.
Lemma lem1149054 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term133 _27073 P h x t) = (term151 _27073 P h x t).
Proof. exact (MK_COMB (@lem1149053 _27073 h P x t) (@lem1149027 _27073 P h x t)). Qed.
Lemma lem1149055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1149056 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term135 _27073 P h x t) = (term152 _27073 P h x t).
Proof. exact (MK_COMB (@lem1149055) (@lem1149054 _27073 P h x t)). Qed.
Lemma lem1149057 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term137 _27073 P h x t) = (term153 _27073 P h x t).
Proof. exact (MK_COMB (@lem1149056 _27073 P h x t) (@lem1148997 _27073 P h x t)). Qed.
Lemma lem1149058 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term88 _27073 P h x t) : term153 _27073 P h x t.
Proof. exact (EQ_MP (@lem1149057 _27073 P h x t) (@lem1148859 _27073 P h x t h1)). Qed.
Lemma lem1149061 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term151 _27073 P h x t) : term151 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1149062 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : term146 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1149063 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term151 _27073 P h x t) : term147 _27073 P h x t.
Proof. exact (proj2 (@lem1149061 _27073 P h x t h1)). Qed.
Lemma lem1149064 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term151 _27073 P h x t) : term149 _27073 h P x t.
Proof. exact (proj1 (@lem1149061 _27073 P h x t h1)). Qed.
Lemma lem1149066 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) : term122 _27073 h x t.
Proof. exact (h1). Qed.
Lemma lem1149068 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term148 _27073 P x t) : term148 _27073 P x t.
Proof. exact (h1). Qed.
Lemma lem1149074 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term148 _27073 P x t) : term148 _27073 P x t.
Proof. exact (h1). Qed.
Lemma lem1149077 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : term139 _27073 P h x t.
Proof. exact (proj2 (@lem1149062 _27073 P h x t h1)). Qed.
Lemma lem1149078 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : term144 _27073 h P x t.
Proof. exact (proj1 (@lem1149062 _27073 P h x t h1)). Qed.
Lemma lem1149079 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : term47 _27073 h x t.
Proof. exact (proj2 (@lem1149077 _27073 P h x t h1)). Qed.
Lemma lem1149081 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : term143 _27073 P x t.
Proof. exact (proj2 (@lem1149078 _27073 P h x t h1)). Qed.
Lemma lem1149138 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1149142 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1149192 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1149258 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1149378 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1149382 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1149440 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1149506 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1149564 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) : term140 _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1149568 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : @List.In _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1149646 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1149648 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1149674 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1149704 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) : term154 _27073 x h.
Proof. exact (proj1 (@lem1149066 _27073 h x t h1)). Qed.
Lemma lem1149708 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1149736 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) : term140 _27073 x t.
Proof. exact (proj2 (@lem1149066 _27073 h x t h1)). Qed.
Lemma lem1149766 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : @I (_27073 -> Prop) P x.
Proof. exact (proj1 (@lem1149077 _27073 P h x t h1)). Qed.
Lemma lem1149770 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1149772 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1149802 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1149832 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : term154 _27073 x h.
Proof. exact (proj1 (@lem1149078 _27073 P h x t h1)). Qed.
Lemma lem1149836 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1149866 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) : term140 _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1149868 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : @List.In _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1149923 {_27073 : Type'} (P : _27073 -> Prop) : (term155 _27073 P) = (term155 _27073 P).
Proof. exact (eq_refl (term155 _27073 P)). Qed.
Lemma lem1149924 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (term156 _27073 P x) = (term156 _27073 P h).
Proof. exact (MK_COMB (@lem1149923 _27073 P) (@lem1149648 _27073 x h h1)). Qed.
Lemma lem1149925 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term156 _27073 P h) = (term141 _27073 P h).
Proof. exact (eq_refl (term156 _27073 P h)). Qed.
Lemma lem1149926 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term157 _27073 P x) = (term157 _27073 P x).
Proof. exact (eq_refl (term157 _27073 P x)). Qed.
Lemma lem1149927 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term156 _27073 P x) = (term156 _27073 P h)) = ((term156 _27073 P x) = (term141 _27073 P h)).
Proof. exact (MK_COMB (@lem1149926 _27073 P x) (@lem1149925 _27073 P h)). Qed.
Lemma lem1149928 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term156 _27073 P x) = (term141 _27073 P x).
Proof. exact (eq_refl (term156 _27073 P x)). Qed.
Lemma lem1149929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1149930 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term157 _27073 P x) = (term158 _27073 P x).
Proof. exact (MK_COMB (@lem1149929) (@lem1149928 _27073 P x)). Qed.
Lemma lem1149931 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term141 _27073 P h) = (term141 _27073 P h).
Proof. exact (eq_refl (term141 _27073 P h)). Qed.
Lemma lem1149932 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term156 _27073 P x) = (term141 _27073 P h)) = ((term141 _27073 P x) = (term141 _27073 P h)).
Proof. exact (MK_COMB (@lem1149930 _27073 P x) (@lem1149931 _27073 P h)). Qed.
Lemma lem1149933 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term156 _27073 P x) = (term156 _27073 P h)) = ((term141 _27073 P x) = (term141 _27073 P h)).
Proof. exact (TRANS (@lem1149927 _27073 x P h) (@lem1149932 _27073 x P h)). Qed.
Lemma lem1149934 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (term141 _27073 P x) = (term141 _27073 P h).
Proof. exact (EQ_MP (@lem1149933 _27073 x P h) (@lem1149924 _27073 P x h h1)). Qed.
Lemma lem1149935 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : x = h) : term141 _27073 P h.
Proof. exact (EQ_MP (@lem1149934 _27073 P x h h2) (@lem1149646 _27073 P x h1)). Qed.
Lemma lem1150006 {_27073 : Type'} (h : _27073) : (term159 _27073 h) = (term159 _27073 h).
Proof. exact (eq_refl (term159 _27073 h)). Qed.
Lemma lem1150007 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : (term160 _27073 h x) = (term161 _27073 h).
Proof. exact (MK_COMB (@lem1150006 _27073 h) (@lem1149708 _27073 x h h1)). Qed.
Lemma lem1150008 {_27073 : Type'} (h : _27073) : (term161 _27073 h) = (term162 _27073 h).
Proof. exact (eq_refl (term161 _27073 h)). Qed.
Lemma lem1150009 {_27073 : Type'} (h : _27073) (x : _27073) : (term163 _27073 h x) = (term163 _27073 h x).
Proof. exact (eq_refl (term163 _27073 h x)). Qed.
Lemma lem1150010 {_27073 : Type'} (x : _27073) (h : _27073) : ((term160 _27073 h x) = (term161 _27073 h)) = ((term160 _27073 h x) = (term162 _27073 h)).
Proof. exact (MK_COMB (@lem1150009 _27073 h x) (@lem1150008 _27073 h)). Qed.
Lemma lem1150011 {_27073 : Type'} (x : _27073) (h : _27073) : (term160 _27073 h x) = (term154 _27073 x h).
Proof. exact (eq_refl (term160 _27073 h x)). Qed.
Lemma lem1150012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1150013 {_27073 : Type'} (x : _27073) (h : _27073) : (term163 _27073 h x) = (term164 _27073 x h).
Proof. exact (MK_COMB (@lem1150012) (@lem1150011 _27073 x h)). Qed.
Lemma lem1150014 {_27073 : Type'} (h : _27073) : (term162 _27073 h) = (term162 _27073 h).
Proof. exact (eq_refl (term162 _27073 h)). Qed.
Lemma lem1150015 {_27073 : Type'} (x : _27073) (h : _27073) : ((term160 _27073 h x) = (term162 _27073 h)) = ((term154 _27073 x h) = (term162 _27073 h)).
Proof. exact (MK_COMB (@lem1150013 _27073 x h) (@lem1150014 _27073 h)). Qed.
Lemma lem1150016 {_27073 : Type'} (x : _27073) (h : _27073) : ((term160 _27073 h x) = (term161 _27073 h)) = ((term154 _27073 x h) = (term162 _27073 h)).
Proof. exact (TRANS (@lem1150010 _27073 x h) (@lem1150015 _27073 x h)). Qed.
Lemma lem1150017 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : (term154 _27073 x h) = (term162 _27073 h).
Proof. exact (EQ_MP (@lem1150016 _27073 x h) (@lem1150007 _27073 x h h1)). Qed.
Lemma lem1150018 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : term162 _27073 h.
Proof. exact (EQ_MP (@lem1150017 _27073 x h h2) (@lem1149704 _27073 h x t h1)). Qed.
Lemma lem1150102 {_27073 : Type'} (P : _27073 -> Prop) : (term165 _27073 P) = (term165 _27073 P).
Proof. exact (eq_refl (term165 _27073 P)). Qed.
Lemma lem1150103 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (term166 _27073 P x) = (term166 _27073 P h).
Proof. exact (MK_COMB (@lem1150102 _27073 P) (@lem1149772 _27073 x h h1)). Qed.
Lemma lem1150104 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term166 _27073 P h) = (@I (_27073 -> Prop) P h).
Proof. exact (eq_refl (term166 _27073 P h)). Qed.
Lemma lem1150105 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term167 _27073 P x) = (term167 _27073 P x).
Proof. exact (eq_refl (term167 _27073 P x)). Qed.
Lemma lem1150106 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term166 _27073 P x) = (term166 _27073 P h)) = ((term166 _27073 P x) = (@I (_27073 -> Prop) P h)).
Proof. exact (MK_COMB (@lem1150105 _27073 P x) (@lem1150104 _27073 P h)). Qed.
Lemma lem1150107 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term166 _27073 P x) = (@I (_27073 -> Prop) P x).
Proof. exact (eq_refl (term166 _27073 P x)). Qed.
Lemma lem1150108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1150109 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term167 _27073 P x) = (term168 _27073 P x).
Proof. exact (MK_COMB (@lem1150108) (@lem1150107 _27073 P x)). Qed.
Lemma lem1150110 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (@I (_27073 -> Prop) P h) = (@I (_27073 -> Prop) P h).
Proof. exact (eq_refl (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1150111 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term166 _27073 P x) = (@I (_27073 -> Prop) P h)) = ((@I (_27073 -> Prop) P x) = (@I (_27073 -> Prop) P h)).
Proof. exact (MK_COMB (@lem1150109 _27073 P x) (@lem1150110 _27073 P h)). Qed.
Lemma lem1150112 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term166 _27073 P x) = (term166 _27073 P h)) = ((@I (_27073 -> Prop) P x) = (@I (_27073 -> Prop) P h)).
Proof. exact (TRANS (@lem1150106 _27073 x P h) (@lem1150111 _27073 x P h)). Qed.
Lemma lem1150113 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (@I (_27073 -> Prop) P x) = (@I (_27073 -> Prop) P h).
Proof. exact (EQ_MP (@lem1150112 _27073 x P h) (@lem1150103 _27073 P x h h1)). Qed.
Lemma lem1150128 {_27073 : Type'} (P : _27073 -> Prop) : (term155 _27073 P) = (term155 _27073 P).
Proof. exact (eq_refl (term155 _27073 P)). Qed.
Lemma lem1150129 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (term156 _27073 P x) = (term156 _27073 P h).
Proof. exact (MK_COMB (@lem1150128 _27073 P) (@lem1149772 _27073 x h h1)). Qed.
Lemma lem1150130 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term156 _27073 P h) = (term141 _27073 P h).
Proof. exact (eq_refl (term156 _27073 P h)). Qed.
Lemma lem1150131 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term157 _27073 P x) = (term157 _27073 P x).
Proof. exact (eq_refl (term157 _27073 P x)). Qed.
Lemma lem1150132 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term156 _27073 P x) = (term156 _27073 P h)) = ((term156 _27073 P x) = (term141 _27073 P h)).
Proof. exact (MK_COMB (@lem1150131 _27073 P x) (@lem1150130 _27073 P h)). Qed.
Lemma lem1150133 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term156 _27073 P x) = (term141 _27073 P x).
Proof. exact (eq_refl (term156 _27073 P x)). Qed.
Lemma lem1150134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1150135 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term157 _27073 P x) = (term158 _27073 P x).
Proof. exact (MK_COMB (@lem1150134) (@lem1150133 _27073 P x)). Qed.
Lemma lem1150136 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term141 _27073 P h) = (term141 _27073 P h).
Proof. exact (eq_refl (term141 _27073 P h)). Qed.
Lemma lem1150137 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term156 _27073 P x) = (term141 _27073 P h)) = ((term141 _27073 P x) = (term141 _27073 P h)).
Proof. exact (MK_COMB (@lem1150135 _27073 P x) (@lem1150136 _27073 P h)). Qed.
Lemma lem1150138 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term156 _27073 P x) = (term156 _27073 P h)) = ((term141 _27073 P x) = (term141 _27073 P h)).
Proof. exact (TRANS (@lem1150132 _27073 x P h) (@lem1150137 _27073 x P h)). Qed.
Lemma lem1150139 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (term141 _27073 P x) = (term141 _27073 P h).
Proof. exact (EQ_MP (@lem1150138 _27073 x P h) (@lem1150129 _27073 P x h h1)). Qed.
Lemma lem1150140 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : x = h) : term141 _27073 P h.
Proof. exact (EQ_MP (@lem1150139 _27073 P x h h2) (@lem1149770 _27073 P x h1)). Qed.
Lemma lem1150224 {_27073 : Type'} (h : _27073) : (term159 _27073 h) = (term159 _27073 h).
Proof. exact (eq_refl (term159 _27073 h)). Qed.
Lemma lem1150225 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : (term160 _27073 h x) = (term161 _27073 h).
Proof. exact (MK_COMB (@lem1150224 _27073 h) (@lem1149836 _27073 x h h1)). Qed.
Lemma lem1150226 {_27073 : Type'} (h : _27073) : (term161 _27073 h) = (term162 _27073 h).
Proof. exact (eq_refl (term161 _27073 h)). Qed.
Lemma lem1150227 {_27073 : Type'} (h : _27073) (x : _27073) : (term163 _27073 h x) = (term163 _27073 h x).
Proof. exact (eq_refl (term163 _27073 h x)). Qed.
Lemma lem1150228 {_27073 : Type'} (x : _27073) (h : _27073) : ((term160 _27073 h x) = (term161 _27073 h)) = ((term160 _27073 h x) = (term162 _27073 h)).
Proof. exact (MK_COMB (@lem1150227 _27073 h x) (@lem1150226 _27073 h)). Qed.
Lemma lem1150229 {_27073 : Type'} (x : _27073) (h : _27073) : (term160 _27073 h x) = (term154 _27073 x h).
Proof. exact (eq_refl (term160 _27073 h x)). Qed.
Lemma lem1150230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1150231 {_27073 : Type'} (x : _27073) (h : _27073) : (term163 _27073 h x) = (term164 _27073 x h).
Proof. exact (MK_COMB (@lem1150230) (@lem1150229 _27073 x h)). Qed.
Lemma lem1150232 {_27073 : Type'} (h : _27073) : (term162 _27073 h) = (term162 _27073 h).
Proof. exact (eq_refl (term162 _27073 h)). Qed.
Lemma lem1150233 {_27073 : Type'} (x : _27073) (h : _27073) : ((term160 _27073 h x) = (term162 _27073 h)) = ((term154 _27073 x h) = (term162 _27073 h)).
Proof. exact (MK_COMB (@lem1150231 _27073 x h) (@lem1150232 _27073 h)). Qed.
Lemma lem1150234 {_27073 : Type'} (x : _27073) (h : _27073) : ((term160 _27073 h x) = (term161 _27073 h)) = ((term154 _27073 x h) = (term162 _27073 h)).
Proof. exact (TRANS (@lem1150228 _27073 x h) (@lem1150233 _27073 x h)). Qed.
Lemma lem1150235 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : (term154 _27073 x h) = (term162 _27073 h).
Proof. exact (EQ_MP (@lem1150234 _27073 x h) (@lem1150225 _27073 x h h1)). Qed.
Lemma lem1150236 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : term162 _27073 h.
Proof. exact (EQ_MP (@lem1150235 _27073 x h h2) (@lem1149832 _27073 P h x t h1)). Qed.
Lemma lem1150279 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (h1 : P h) : @I (_27073 -> Prop) P h.
Proof. exact (EQ_MP (@lem1148939 _27073 P h) (@lem1148799 _27073 P h h1)). Qed.
Lemma lem1150280 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (h1 : P h) : term169 _27073 P h.
Proof. exact (fun h0 : term141 _27073 P h => @lem1150279 _27073 P h h1). Qed.
Lemma lem1150282 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150283 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term169 _27073 P h) = (@I (_27073 -> Prop) P h).
Proof. exact (@lem1150282 (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1150284 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (h1 : P h) : @I (_27073 -> Prop) P h.
Proof. exact (EQ_MP (@lem1150283 _27073 P h) (@lem1150280 _27073 P h h1)). Qed.
Lemma lem1150287 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1150289 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term141 _27073 P h) = (term171 _27073 P h).
Proof. exact (@lem1150287 (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1150292 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : x = h) : term171 _27073 P h.
Proof. exact (EQ_MP (@lem1150289 _27073 P h) (@lem1149935 _27073 P x h h1 h2)). Qed.
Lemma lem1150295 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : False.
Proof. exact (@lem1150292 _27073 P x h h1 h3 (@lem1150284 _27073 P h h2)). Qed.
Lemma lem1150296 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : term172.
Proof. exact (fun h0 : ~ False => @lem1150295 _27073 P x h h1 h2 h3). Qed.
Lemma lem1150298 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150299 : term172 = False.
Proof. exact (@lem1150298 False). Qed.
Lemma lem1150302 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term148 _27073 P x t) : @I (_27073 -> Prop) P x.
Proof. exact (proj1 (@lem1149068 _27073 P x t h1)). Qed.
Lemma lem1150303 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term148 _27073 P x t) : term169 _27073 P x.
Proof. exact (fun h0 : term141 _27073 P x => @lem1150302 _27073 P x t h1). Qed.
Lemma lem1150305 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150306 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term169 _27073 P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1150305 (@I (_27073 -> Prop) P x)). Qed.
Lemma lem1150307 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term148 _27073 P x t) : @I (_27073 -> Prop) P x.
Proof. exact (EQ_MP (@lem1150306 _27073 P x) (@lem1150303 _27073 P x t h1)). Qed.
Lemma lem1150310 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1150312 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term141 _27073 P x) = (term171 _27073 P x).
Proof. exact (@lem1150310 (@I (_27073 -> Prop) P x)). Qed.
Lemma lem1150315 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term171 _27073 P x.
Proof. exact (EQ_MP (@lem1150312 _27073 P x) (@lem1149674 _27073 P x h1)). Qed.
Lemma lem1150318 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term148 _27073 P x t) : False.
Proof. exact (@lem1150315 _27073 P x h1 (@lem1150307 _27073 P x t h2)). Qed.
Lemma lem1150319 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term148 _27073 P x t) : term172.
Proof. exact (fun h0 : ~ False => @lem1150318 _27073 P x t h1 h2). Qed.
Lemma lem1150321 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150322 : term172 = False.
Proof. exact (@lem1150321 False). Qed.
Lemma lem1150323 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term148 _27073 P x t) : False.
Proof. exact (EQ_MP (@lem1150322) (@lem1150319 _27073 P x t h1 h2)). Qed.
Lemma lem1150384 {_27073 : Type'} (x : _27073) : x = x.
Proof. exact (@lem21386 _27073 x). Qed.
Lemma lem1150385 {_27073 : Type'} (x : _27073) : x = x.
Proof. exact (@lem1150384 _27073 x). Qed.
Lemma lem1150386 {_27073 : Type'} (h : _27073) : h = h.
Proof. exact (@lem1150385 _27073 h). Qed.
Lemma lem1150387 {_27073 : Type'} (h : _27073) : term173 _27073 h.
Proof. exact (fun h0 : term162 _27073 h => @lem1150386 _27073 h). Qed.
Lemma lem1150389 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150390 {_27073 : Type'} (h : _27073) : (term173 _27073 h) = (h = h).
Proof. exact (@lem1150389 (h = h)). Qed.
Lemma lem1150391 {_27073 : Type'} (h : _27073) : h = h.
Proof. exact (EQ_MP (@lem1150390 _27073 h) (@lem1150387 _27073 h)). Qed.
Lemma lem1150394 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1150396 {_27073 : Type'} (h : _27073) : (term162 _27073 h) = (term174 _27073 h).
Proof. exact (@lem1150394 (h = h)). Qed.
Lemma lem1150399 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : term174 _27073 h.
Proof. exact (EQ_MP (@lem1150396 _27073 h) (@lem1150018 _27073 t x h h1 h2)). Qed.
Lemma lem1150402 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : False.
Proof. exact (@lem1150399 _27073 t x h h1 h2 (@lem1150391 _27073 h)). Qed.
Lemma lem1150403 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : term172.
Proof. exact (fun h0 : ~ False => @lem1150402 _27073 t x h h1 h2). Qed.
Lemma lem1150405 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150406 : term172 = False.
Proof. exact (@lem1150405 False). Qed.
Lemma lem1150468 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term148 _27073 P x t) : @List.In _27073 x t.
Proof. exact (proj2 (@lem1149074 _27073 P x t h1)). Qed.
Lemma lem1150469 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term148 _27073 P x t) : term175 _27073 x t.
Proof. exact (fun h0 : term140 _27073 x t => @lem1150468 _27073 P x t h1). Qed.
Lemma lem1150471 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150472 {_27073 : Type'} (x : _27073) (t : list _27073) : (term175 _27073 x t) = (@List.In _27073 x t).
Proof. exact (@lem1150471 (@List.In _27073 x t)). Qed.
Lemma lem1150473 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term148 _27073 P x t) : @List.In _27073 x t.
Proof. exact (EQ_MP (@lem1150472 _27073 x t) (@lem1150469 _27073 P x t h1)). Qed.
Lemma lem1150476 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1150478 {_27073 : Type'} (x : _27073) (t : list _27073) : (term140 _27073 x t) = (term176 _27073 x t).
Proof. exact (@lem1150476 (@List.In _27073 x t)). Qed.
Lemma lem1150481 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) : term176 _27073 x t.
Proof. exact (EQ_MP (@lem1150478 _27073 x t) (@lem1149736 _27073 h x t h1)). Qed.
Lemma lem1150484 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) (h2 : term148 _27073 P x t) : False.
Proof. exact (@lem1150481 _27073 h x t h1 (@lem1150473 _27073 P x t h2)). Qed.
Lemma lem1150485 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) (h2 : term148 _27073 P x t) : term172.
Proof. exact (fun h0 : ~ False => @lem1150484 _27073 h P x t h1 h2). Qed.
Lemma lem1150487 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150488 : term172 = False.
Proof. exact (@lem1150487 False). Qed.
Lemma lem1150489 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) (h2 : term148 _27073 P x t) : False.
Proof. exact (EQ_MP (@lem1150488) (@lem1150485 _27073 h P x t h1 h2)). Qed.
Lemma lem1150550 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : @I (_27073 -> Prop) P h.
Proof. exact (EQ_MP (@lem1150113 _27073 P x h h2) (@lem1149766 _27073 P h x t h1)). Qed.
Lemma lem1150551 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : term169 _27073 P h.
Proof. exact (fun h0 : term141 _27073 P h => @lem1150550 _27073 P t x h h1 h2). Qed.
Lemma lem1150553 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150554 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term169 _27073 P h) = (@I (_27073 -> Prop) P h).
Proof. exact (@lem1150553 (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1150555 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : @I (_27073 -> Prop) P h.
Proof. exact (EQ_MP (@lem1150554 _27073 P h) (@lem1150551 _27073 P t x h h1 h2)). Qed.
Lemma lem1150558 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1150560 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term141 _27073 P h) = (term171 _27073 P h).
Proof. exact (@lem1150558 (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1150563 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : x = h) : term171 _27073 P h.
Proof. exact (EQ_MP (@lem1150560 _27073 P h) (@lem1150140 _27073 P x h h1 h2)). Qed.
Lemma lem1150566 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (@lem1150563 _27073 P x h h1 h3 (@lem1150555 _27073 P t x h h2 h3)). Qed.
Lemma lem1150567 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : term172.
Proof. exact (fun h0 : ~ False => @lem1150566 _27073 P t x h h1 h2 h3). Qed.
Lemma lem1150569 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150570 : term172 = False.
Proof. exact (@lem1150569 False). Qed.
Lemma lem1150632 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : @I (_27073 -> Prop) P x.
Proof. exact (proj1 (@lem1149077 _27073 P h x t h1)). Qed.
Lemma lem1150633 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : term169 _27073 P x.
Proof. exact (fun h0 : term141 _27073 P x => @lem1150632 _27073 P h x t h1). Qed.
Lemma lem1150635 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150636 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term169 _27073 P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1150635 (@I (_27073 -> Prop) P x)). Qed.
Lemma lem1150637 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : @I (_27073 -> Prop) P x.
Proof. exact (EQ_MP (@lem1150636 _27073 P x) (@lem1150633 _27073 P h x t h1)). Qed.
Lemma lem1150640 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1150642 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term141 _27073 P x) = (term171 _27073 P x).
Proof. exact (@lem1150640 (@I (_27073 -> Prop) P x)). Qed.
Lemma lem1150645 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term171 _27073 P x.
Proof. exact (EQ_MP (@lem1150642 _27073 P x) (@lem1149802 _27073 P x h1)). Qed.
Lemma lem1150648 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : False.
Proof. exact (@lem1150645 _27073 P x h1 (@lem1150637 _27073 P h x t h2)). Qed.
Lemma lem1150649 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : term172.
Proof. exact (fun h0 : ~ False => @lem1150648 _27073 P h x t h1 h2). Qed.
Lemma lem1150651 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150652 : term172 = False.
Proof. exact (@lem1150651 False). Qed.
Lemma lem1150653 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1150652) (@lem1150649 _27073 P h x t h1 h2)). Qed.
Lemma lem1150714 {_27073 : Type'} (x : _27073) : x = x.
Proof. exact (@lem21386 _27073 x). Qed.
Lemma lem1150715 {_27073 : Type'} (x : _27073) : x = x.
Proof. exact (@lem1150714 _27073 x). Qed.
Lemma lem1150716 {_27073 : Type'} (h : _27073) : h = h.
Proof. exact (@lem1150715 _27073 h). Qed.
Lemma lem1150717 {_27073 : Type'} (h : _27073) : term173 _27073 h.
Proof. exact (fun h0 : term162 _27073 h => @lem1150716 _27073 h). Qed.
Lemma lem1150719 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150720 {_27073 : Type'} (h : _27073) : (term173 _27073 h) = (h = h).
Proof. exact (@lem1150719 (h = h)). Qed.
Lemma lem1150721 {_27073 : Type'} (h : _27073) : h = h.
Proof. exact (EQ_MP (@lem1150720 _27073 h) (@lem1150717 _27073 h)). Qed.
Lemma lem1150724 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1150726 {_27073 : Type'} (h : _27073) : (term162 _27073 h) = (term174 _27073 h).
Proof. exact (@lem1150724 (h = h)). Qed.
Lemma lem1150729 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : term174 _27073 h.
Proof. exact (EQ_MP (@lem1150726 _27073 h) (@lem1150236 _27073 P t x h h1 h2)). Qed.
Lemma lem1150732 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : False.
Proof. exact (@lem1150729 _27073 P t x h h1 h2 (@lem1150721 _27073 h)). Qed.
Lemma lem1150733 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : term172.
Proof. exact (fun h0 : ~ False => @lem1150732 _27073 P t x h h1 h2). Qed.
Lemma lem1150735 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150736 : term172 = False.
Proof. exact (@lem1150735 False). Qed.
Lemma lem1150798 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : @List.In _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1150799 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : term175 _27073 x t.
Proof. exact (fun h0 : term140 _27073 x t => @lem1150798 _27073 x t h1). Qed.
Lemma lem1150801 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150802 {_27073 : Type'} (x : _27073) (t : list _27073) : (term175 _27073 x t) = (@List.In _27073 x t).
Proof. exact (@lem1150801 (@List.In _27073 x t)). Qed.
Lemma lem1150803 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : @List.In _27073 x t.
Proof. exact (EQ_MP (@lem1150802 _27073 x t) (@lem1150799 _27073 x t h1)). Qed.
Lemma lem1150806 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1150808 {_27073 : Type'} (x : _27073) (t : list _27073) : (term140 _27073 x t) = (term176 _27073 x t).
Proof. exact (@lem1150806 (@List.In _27073 x t)). Qed.
Lemma lem1150811 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) : term176 _27073 x t.
Proof. exact (EQ_MP (@lem1150808 _27073 x t) (@lem1149866 _27073 x t h1)). Qed.
Lemma lem1150814 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (@lem1150811 _27073 x t h1 (@lem1150803 _27073 x t h2)). Qed.
Lemma lem1150815 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : term172.
Proof. exact (fun h0 : ~ False => @lem1150814 _27073 x t h1 h2). Qed.
Lemma lem1150817 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1150818 : term172 = False.
Proof. exact (@lem1150817 False). Qed.
Lemma lem1150819 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1150818) (@lem1150815 _27073 x t h1 h2)). Qed.
Lemma lem1150820 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1150736) (@lem1150733 _27073 P t x h h1 h2)). Qed.
Lemma lem1150821 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150570) (@lem1150567 _27073 P t x h h1 h2 h3)). Qed.
Lemma lem1150822 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1150406) (@lem1150403 _27073 t x h h1 h2)). Qed.
Lemma lem1150823 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150299) (@lem1150296 _27073 P x h h1 h2 h3)). Qed.
Lemma lem1150824 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (@List.In _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _27073 x t => @lem1150819 _27073 x t h1 h2) (fun h3 : False => @lem1149868 _27073 x t h2)). Qed.
Lemma lem1150825 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1150824 _27073 x t h1 h2) (@lem1149868 _27073 x t h2)). Qed.
Lemma lem1150826 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (term140 _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : term140 _27073 x t => @lem1150825 _27073 x t h1 h2) (fun h3 : False => @lem1149866 _27073 x t h1)). Qed.
Lemma lem1150827 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1150826 _27073 x t h1 h2) (@lem1149866 _27073 x t h1)). Qed.
Lemma lem1150828 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1150820 _27073 P t x h h1 h2) (fun h3 : False => @lem1149836 _27073 x h h2)). Qed.
Lemma lem1150829 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1150828 _27073 P t x h h1 h2) (@lem1149836 _27073 x h h2)). Qed.
Lemma lem1150830 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1150653 _27073 P h x t h1 h2) (fun h3 : False => @lem1149802 _27073 P x h1)). Qed.
Lemma lem1150831 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1150830 _27073 P h x t h1 h2) (@lem1149802 _27073 P x h1)). Qed.
Lemma lem1150832 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1150821 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1149772 _27073 x h h3)). Qed.
Lemma lem1150833 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150832 _27073 P t x h h1 h2 h3) (@lem1149772 _27073 x h h3)). Qed.
Lemma lem1150834 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h4 : term141 _27073 P x => @lem1150833 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1149770 _27073 P x h1)). Qed.
Lemma lem1150835 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150834 _27073 P t x h h1 h2 h3) (@lem1149770 _27073 P x h1)). Qed.
Lemma lem1150836 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1150822 _27073 t x h h1 h2) (fun h3 : False => @lem1149708 _27073 x h h2)). Qed.
Lemma lem1150837 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1150836 _27073 t x h h1 h2) (@lem1149708 _27073 x h h2)). Qed.
Lemma lem1150838 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term148 _27073 P x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1150323 _27073 P x t h1 h2) (fun h3 : False => @lem1149674 _27073 P x h1)). Qed.
Lemma lem1150839 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term148 _27073 P x t) : False.
Proof. exact (EQ_MP (@lem1150838 _27073 P x t h1 h2) (@lem1149674 _27073 P x h1)). Qed.
Lemma lem1150840 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1150823 _27073 P x h h1 h2 h3) (fun h4 : False => @lem1149648 _27073 x h h3)). Qed.
Lemma lem1150841 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150840 _27073 P x h h1 h2 h3) (@lem1149648 _27073 x h h3)). Qed.
Lemma lem1150842 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h4 : term141 _27073 P x => @lem1150841 _27073 P x h h1 h2 h3) (fun h4 : False => @lem1149646 _27073 P x h1)). Qed.
Lemma lem1150843 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150842 _27073 P x h h1 h2 h3) (@lem1149646 _27073 P x h1)). Qed.
Lemma lem1150844 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (@List.In _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _27073 x t => @lem1150827 _27073 x t h1 h2) (fun h3 : False => @lem1149568 _27073 x t h2)). Qed.
Lemma lem1150845 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1150844 _27073 x t h1 h2) (@lem1149568 _27073 x t h2)). Qed.
Lemma lem1150846 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (term140 _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : term140 _27073 x t => @lem1150845 _27073 x t h1 h2) (fun h3 : False => @lem1149564 _27073 x t h1)). Qed.
Lemma lem1150847 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1150846 _27073 x t h1 h2) (@lem1149564 _27073 x t h1)). Qed.
Lemma lem1150848 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1150829 _27073 P t x h h1 h2) (fun h3 : False => @lem1149506 _27073 x h h2)). Qed.
Lemma lem1150849 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1150848 _27073 P t x h h1 h2) (@lem1149506 _27073 x h h2)). Qed.
Lemma lem1150850 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1150831 _27073 P h x t h1 h2) (fun h3 : False => @lem1149440 _27073 P x h1)). Qed.
Lemma lem1150851 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1150850 _27073 P h x t h1 h2) (@lem1149440 _27073 P x h1)). Qed.
Lemma lem1150852 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1150835 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1149382 _27073 x h h3)). Qed.
Lemma lem1150853 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150852 _27073 P t x h h1 h2 h3) (@lem1149382 _27073 x h h3)). Qed.
Lemma lem1150854 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h4 : term141 _27073 P x => @lem1150853 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1149378 _27073 P x h1)). Qed.
Lemma lem1150855 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150854 _27073 P t x h h1 h2 h3) (@lem1149378 _27073 P x h1)). Qed.
Lemma lem1150856 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1150837 _27073 t x h h1 h2) (fun h3 : False => @lem1149258 _27073 x h h2)). Qed.
Lemma lem1150857 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1150856 _27073 t x h h1 h2) (@lem1149258 _27073 x h h2)). Qed.
Lemma lem1150858 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term148 _27073 P x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1150839 _27073 P x t h1 h2) (fun h3 : False => @lem1149192 _27073 P x h1)). Qed.
Lemma lem1150859 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term148 _27073 P x t) : False.
Proof. exact (EQ_MP (@lem1150858 _27073 P x t h1 h2) (@lem1149192 _27073 P x h1)). Qed.
Lemma lem1150860 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1150843 _27073 P x h h1 h2 h3) (fun h4 : False => @lem1149142 _27073 x h h3)). Qed.
Lemma lem1150861 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150860 _27073 P x h h1 h2 h3) (@lem1149142 _27073 x h h3)). Qed.
Lemma lem1150862 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h4 : term141 _27073 P x => @lem1150861 _27073 P x h h1 h2 h3) (fun h4 : False => @lem1149138 _27073 P x h1)). Qed.
Lemma lem1150863 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150862 _27073 P x h h1 h2 h3) (@lem1149138 _27073 P x h1)). Qed.
Lemma lem1150864 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (@List.In _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _27073 x t => @lem1150847 _27073 x t h1 h2) (fun h3 : False => @lem1149568 _27073 x t h2)). Qed.
Lemma lem1150865 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1150864 _27073 x t h1 h2) (@lem1149568 _27073 x t h2)). Qed.
Lemma lem1150866 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (term140 _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : term140 _27073 x t => @lem1150865 _27073 x t h1 h2) (fun h3 : False => @lem1149564 _27073 x t h1)). Qed.
Lemma lem1150867 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1150866 _27073 x t h1 h2) (@lem1149564 _27073 x t h1)). Qed.
Lemma lem1150868 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1150849 _27073 P t x h h1 h2) (fun h3 : False => @lem1149506 _27073 x h h2)). Qed.
Lemma lem1150869 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term146 _27073 P h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1150868 _27073 P t x h h1 h2) (@lem1149506 _27073 x h h2)). Qed.
Lemma lem1150870 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1150851 _27073 P h x t h1 h2) (fun h3 : False => @lem1149440 _27073 P x h1)). Qed.
Lemma lem1150871 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1150870 _27073 P h x t h1 h2) (@lem1149440 _27073 P x h1)). Qed.
Lemma lem1150872 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1150855 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1149382 _27073 x h h3)). Qed.
Lemma lem1150873 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150872 _27073 P t x h h1 h2 h3) (@lem1149382 _27073 x h h3)). Qed.
Lemma lem1150874 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h4 : term141 _27073 P x => @lem1150873 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1149378 _27073 P x h1)). Qed.
Lemma lem1150875 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150874 _27073 P t x h h1 h2 h3) (@lem1149378 _27073 P x h1)). Qed.
Lemma lem1150876 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1150857 _27073 t x h h1 h2) (fun h3 : False => @lem1149258 _27073 x h h2)). Qed.
Lemma lem1150877 {_27073 : Type'} (t : list _27073) (x : _27073) (h : _27073) (h1 : term122 _27073 h x t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1150876 _27073 t x h h1 h2) (@lem1149258 _27073 x h h2)). Qed.
Lemma lem1150878 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term148 _27073 P x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1150859 _27073 P x t h1 h2) (fun h3 : False => @lem1149192 _27073 P x h1)). Qed.
Lemma lem1150879 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term148 _27073 P x t) : False.
Proof. exact (EQ_MP (@lem1150878 _27073 P x t h1 h2) (@lem1149192 _27073 P x h1)). Qed.
Lemma lem1150880 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1150863 _27073 P x h h1 h2 h3) (fun h4 : False => @lem1149142 _27073 x h h3)). Qed.
Lemma lem1150881 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150880 _27073 P x h h1 h2 h3) (@lem1149142 _27073 x h h3)). Qed.
Lemma lem1150882 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h4 : term141 _27073 P x => @lem1150881 _27073 P x h h1 h2 h3) (fun h4 : False => @lem1149138 _27073 P x h1)). Qed.
Lemma lem1150883 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1150882 _27073 P x h h1 h2 h3) (@lem1149138 _27073 P x h1)). Qed.
Lemma lem1150884 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : term146 _27073 P h x t) : False.
Proof. exact (or_elim (@lem1149079 _27073 P h x t h2) (fun h0 : x = h => @lem1150869 _27073 P t x h h2 h0) (fun h0 : @List.In _27073 x t => @lem1150867 _27073 x t h1 h0)). Qed.
Lemma lem1150885 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term146 _27073 P h x t) : False.
Proof. exact (or_elim (@lem1149079 _27073 P h x t h2) (fun h0 : x = h => @lem1150875 _27073 P t x h h1 h2 h0) (fun h0 : @List.In _27073 x t => @lem1150871 _27073 P h x t h1 h2)). Qed.
Lemma lem1150886 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term146 _27073 P h x t) : False.
Proof. exact (or_elim (@lem1149081 _27073 P h x t h1) (fun h0 : term141 _27073 P x => @lem1150885 _27073 P h x t h0 h1) (fun h0 : term140 _27073 x t => @lem1150884 _27073 P h x t h0 h1)). Qed.
Lemma lem1150887 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) (h2 : term151 _27073 P h x t) : False.
Proof. exact (or_elim (@lem1149064 _27073 P h x t h2) (fun h0 : x = h => @lem1150877 _27073 t x h h1 h0) (fun h0 : term148 _27073 P x t => @lem1150489 _27073 h P x t h1 h0)). Qed.
Lemma lem1150888 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : P h) (h3 : term151 _27073 P h x t) : False.
Proof. exact (or_elim (@lem1149064 _27073 P h x t h3) (fun h0 : x = h => @lem1150883 _27073 P x h h1 h2 h0) (fun h0 : term148 _27073 P x t => @lem1150879 _27073 P x t h1 h0)). Qed.
Lemma lem1150889 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : P h) (h2 : term151 _27073 P h x t) : False.
Proof. exact (or_elim (@lem1149063 _27073 P h x t h2) (fun h0 : term141 _27073 P x => @lem1150888 _27073 P h x t h0 h1 h2) (fun h0 : term122 _27073 h x t => @lem1150887 _27073 P h x t h0 h2)). Qed.
Lemma lem1150890 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term88 _27073 P h x t) (h2 : P h) : False.
Proof. exact (or_elim (@lem1149058 _27073 P h x t h1) (fun h0 : term151 _27073 P h x t => @lem1150889 _27073 P h x t h2 h0) (fun h0 : term146 _27073 P h x t => @lem1150886 _27073 P h x t h0)). Qed.
Lemma lem1150891 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term88 _27073 P h x t) (h2 : P h) : (P h) = False.
Proof. exact (prop_ext (fun h3 : P h => @lem1150890 _27073 x t P h h1 h2) (fun h3 : False => @lem1148799 _27073 P h h2)). Qed.
Lemma lem1150892 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term88 _27073 P h x t) (h2 : P h) : False.
Proof. exact (EQ_MP (@lem1150891 _27073 x t P h h1 h2) (@lem1148799 _27073 P h h2)). Qed.
Lemma lem1150893 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term88 _27073 P h x t) (h2 : P h) : (term88 _27073 P h x t) = False.
Proof. exact (prop_ext (fun h3 : term88 _27073 P h x t => @lem1150892 _27073 x t P h h1 h2) (fun h3 : False => @lem1148638 _27073 P h x t h1)). Qed.
Lemma lem1150894 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term88 _27073 P h x t) (h2 : P h) : False.
Proof. exact (EQ_MP (@lem1150893 _27073 x t P h h1 h2) (@lem1148638 _27073 P h x t h1)). Qed.
Lemma lem1150895 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : P h) : term87 _27073 P h x t.
Proof. exact (fun h0 : term88 _27073 P h x t => @lem1150894 _27073 x t P h h0 h1). Qed.
Lemma lem1150896 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : P h) : (term81 _27073 h P x t) = (term49 _27073 P h x t).
Proof. exact (EQ_MP (@lem1148637 _27073 P h x t) (@lem1150895 _27073 x t P h h1)). Qed.
Lemma lem1150897 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term96 _27073 P h x t.
Proof. exact (fun h0 : P h => @lem1150896 _27073 x t P h h0). Qed.
Lemma lem1150898 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term97 _27073 P h x t.
Proof. exact (fun h0 : term8 _27073 P t => @lem1150897 _27073 P h x t). Qed.
Lemma lem1150903 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : term101 _27073 h x t.
Proof. exact (fun P : _27073 -> Prop => @lem1150898 _27073 P h x t). Qed.
Lemma lem1150908 {_27073 : Type'} (x : _27073) (t : list _27073) : term105 _27073 x t.
Proof. exact (fun h : _27073 => @lem1150903 _27073 h x t). Qed.
Lemma lem1150913 {_27073 : Type'} (t : list _27073) : term109 _27073 t.
Proof. exact (fun x : _27073 => @lem1150908 _27073 x t). Qed.
Lemma lem1150918 {_27073 : Type'} : term113 _27073.
Proof. exact (fun t : list _27073 => @lem1150913 _27073 t). Qed.
Lemma lem1150919 {_27073 : Type'} : term112 _27073.
Proof. exact (EQ_MP (@lem1148631 _27073) (@lem1150918 _27073)). Qed.
Lemma lem1150920 {_27073 : Type'} (t : list _27073) : term177 _27073 t.
Proof. exact (@lem1150919 _27073 t). Qed.
Lemma lem1150921 {_27073 : Type'} (t : list _27073) : (term177 _27073 t) = (term108 _27073 t).
Proof. exact (eq_refl (term177 _27073 t)). Qed.
Lemma lem1150922 {_27073 : Type'} (t : list _27073) : term108 _27073 t.
Proof. exact (EQ_MP (@lem1150921 _27073 t) (@lem1150920 _27073 t)). Qed.
Lemma lem1150923 {_27073 : Type'} (t : list _27073) (x : _27073) : term178 _27073 t x.
Proof. exact (@lem1150922 _27073 t x). Qed.
Lemma lem1150924 {_27073 : Type'} (x : _27073) (t : list _27073) : (term178 _27073 t x) = (term104 _27073 x t).
Proof. exact (eq_refl (term178 _27073 t x)). Qed.
Lemma lem1150925 {_27073 : Type'} (x : _27073) (t : list _27073) : term104 _27073 x t.
Proof. exact (EQ_MP (@lem1150924 _27073 x t) (@lem1150923 _27073 t x)). Qed.
Lemma lem1150926 {_27073 : Type'} (x : _27073) (t : list _27073) (h : _27073) : term179 _27073 x t h.
Proof. exact (@lem1150925 _27073 x t h). Qed.
Lemma lem1150927 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term179 _27073 x t h) = (term100 _27073 h x t).
Proof. exact (eq_refl (term179 _27073 x t h)). Qed.
Lemma lem1150928 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : term100 _27073 h x t.
Proof. exact (EQ_MP (@lem1150927 _27073 h x t) (@lem1150926 _27073 x t h)). Qed.
Lemma lem1150929 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) (P : _27073 -> Prop) : term180 _27073 h x t P.
Proof. exact (@lem1150928 _27073 h x t P). Qed.
Lemma lem1150930 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term180 _27073 h x t P) = (term89 _27073 P h x t).
Proof. exact (eq_refl (term180 _27073 h x t P)). Qed.
Lemma lem1150931 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term89 _27073 P h x t.
Proof. exact (EQ_MP (@lem1150930 _27073 P h x t) (@lem1150929 _27073 h x t P)). Qed.
Lemma lem1150933 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term89 _27073 P h x t.
Proof. exact (@lem1148450 _27073 P h x t (@lem1150931 _27073 P h x t)). Qed.
Lemma lem1150934 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term95 _27073 P h x t.
Proof. exact (@lem1150933 _27073 P h x t (@lem1148216 _27073 P t h1)). Qed.
Lemma lem1150935 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : P h) : term87 _27073 P h x t.
Proof. exact (@lem1150934 _27073 h x P t h1 (@lem1148329 _27073 P h h2)). Qed.
Lemma lem1150936 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : term88 _27073 P h x t) (h3 : P h) : False.
Proof. exact (@lem1150935 _27073 x t P h h1 h3 (@lem1148434 _27073 P h x t h2)). Qed.
Lemma lem1150937 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : term88 _27073 P h x t) (h3 : P h) : (term88 _27073 P h x t) = False.
Proof. exact (prop_ext (fun h4 : term88 _27073 P h x t => @lem1150936 _27073 x t P h h1 h2 h3) (fun h4 : False => @lem1148434 _27073 P h x t h2)). Qed.
Lemma lem1150938 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : term88 _27073 P h x t) (h3 : P h) : False.
Proof. exact (EQ_MP (@lem1150937 _27073 x t P h h1 h2 h3) (@lem1148434 _27073 P h x t h2)). Qed.
Lemma lem1150939 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : P h) : term87 _27073 P h x t.
Proof. exact (fun h0 : term88 _27073 P h x t => @lem1150938 _27073 x t P h h1 h0 h2). Qed.
Lemma lem1150940 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : P h) : (term81 _27073 h P x t) = (term49 _27073 P h x t).
Proof. exact (EQ_MP (@lem1148433 _27073 P h x t) (@lem1150939 _27073 x t P h h1 h2)). Qed.
Lemma lem1150942 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1150943 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : ((term78 _27073 P x t) = (term49 _27073 P h x t)) = (term181 _27073 P h x t).
Proof. exact (@lem1150942 ((term78 _27073 P x t) = (term49 _27073 P h x t))). Qed.
Lemma lem1150944 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term181 _27073 P h x t) = ((term78 _27073 P x t) = (term49 _27073 P h x t)).
Proof. exact (SYM (@lem1150943 _27073 P h x t)). Qed.
Lemma lem1150945 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term182 _27073 P h x t) : term182 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1150948 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term183 _27073 P h x t) : term183 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1150949 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term184 _27073 P h x t.
Proof. exact (fun h0 : term183 _27073 P h x t => @lem1150948 _27073 P h x t h0). Qed.
Lemma lem1150950 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term184 _27073 P h x t) : term184 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1150951 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term183 _27073 P h x t) : term183 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1150952 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term183 _27073 P h x t) (h2 : term184 _27073 P h x t) : term183 _27073 P h x t.
Proof. exact (@lem1150950 _27073 P h x t h2 (@lem1150951 _27073 P h x t h1)). Qed.
Lemma lem1150953 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term183 _27073 P h x t) : term185 _27073 P h x t.
Proof. exact (fun h0 : term184 _27073 P h x t => @lem1150952 _27073 P h x t h1 h0). Qed.
Lemma lem1150954 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term184 _27073 P h x t) : term184 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1150955 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term183 _27073 P h x t) (h2 : term184 _27073 P h x t) : term183 _27073 P h x t.
Proof. exact (@lem1150953 _27073 P h x t h1 (@lem1150954 _27073 P h x t h2)). Qed.
Lemma lem1150956 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term184 _27073 P h x t) : term184 _27073 P h x t.
Proof. exact (fun h0 : term183 _27073 P h x t => @lem1150955 _27073 P h x t h0 h1). Qed.
Lemma lem1150957 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term186 _27073 P h x t.
Proof. exact (fun h0 : term184 _27073 P h x t => @lem1150956 _27073 P h x t h0). Qed.
Lemma lem1150960 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term184 _27073 P h x t.
Proof. exact (@lem1150957 _27073 P h x t (@lem1150949 _27073 P h x t)). Qed.
Lemma lem1150961 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term184 _27073 P h x t.
Proof. exact (@lem1150960 _27073 P h x t). Qed.
Lemma lem1150989 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1150990 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term181 _27073 P h x t) = (term187 _27073 P h x t).
Proof. exact (@lem1150989 (term182 _27073 P h x t)). Qed.
Lemma lem1150992 (t : Prop) : (term94 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1150993 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term187 _27073 P h x t) = ((term78 _27073 P x t) = (term49 _27073 P h x t)).
Proof. exact (@lem1150992 ((term78 _27073 P x t) = (term49 _27073 P h x t))). Qed.
Lemma lem1150994 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term181 _27073 P h x t) = ((term78 _27073 P x t) = (term49 _27073 P h x t)).
Proof. exact (TRANS (@lem1150990 _27073 P h x t) (@lem1150993 _27073 P h x t)). Qed.
Lemma lem1151001 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term63 _27073 P h) = (term63 _27073 P h).
Proof. exact (eq_refl (term63 _27073 P h)). Qed.
Lemma lem1151002 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term188 _27073 P h x t) = (term189 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151001 _27073 P h) (@lem1150994 _27073 P h x t)). Qed.
Lemma lem1151005 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term10 _27073 P t) = (term10 _27073 P t).
Proof. exact (eq_refl (term10 _27073 P t)). Qed.
Lemma lem1151006 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term183 _27073 P h x t) = (term190 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151005 _27073 P t) (@lem1151002 _27073 P h x t)). Qed.
Lemma lem1151009 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term191 _27073 h x t) = (term192 _27073 h x t).
Proof. exact (fun_ext (fun P : _27073 -> Prop => @lem1151006 _27073 P h x t)). Qed.
Lemma lem1151010 {_27073 : Type'} : (@all (_27073 -> Prop)) = (@all (_27073 -> Prop)).
Proof. exact (eq_refl (@all (_27073 -> Prop))). Qed.
Lemma lem1151011 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term193 _27073 h x t) = (term194 _27073 h x t).
Proof. exact (MK_COMB (@lem1151010 _27073) (@lem1151009 _27073 h x t)). Qed.
Lemma lem1151016 {_27073 : Type'} (x : _27073) (t : list _27073) : (term195 _27073 x t) = (term196 _27073 x t).
Proof. exact (fun_ext (fun h : _27073 => @lem1151011 _27073 h x t)). Qed.
Lemma lem1151017 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1151018 {_27073 : Type'} (x : _27073) (t : list _27073) : (term197 _27073 x t) = (term198 _27073 x t).
Proof. exact (MK_COMB (@lem1151017 _27073) (@lem1151016 _27073 x t)). Qed.
Lemma lem1151023 {_27073 : Type'} (t : list _27073) : (term199 _27073 t) = (term200 _27073 t).
Proof. exact (fun_ext (fun x : _27073 => @lem1151018 _27073 x t)). Qed.
Lemma lem1151024 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1151025 {_27073 : Type'} (t : list _27073) : (term201 _27073 t) = (term202 _27073 t).
Proof. exact (MK_COMB (@lem1151024 _27073) (@lem1151023 _27073 t)). Qed.
Lemma lem1151030 {_27073 : Type'} : (term203 _27073) = (term204 _27073).
Proof. exact (fun_ext (fun t : list _27073 => @lem1151025 _27073 t)). Qed.
Lemma lem1151031 {_27073 : Type'} : (@all (list _27073)) = (@all (list _27073)).
Proof. exact (eq_refl (@all (list _27073))). Qed.
Lemma lem1151040 {_27073 : Type'} : (term205 _27073) = (term206 _27073).
Proof. exact (MK_COMB (@lem1151031 _27073) (@lem1151030 _27073)). Qed.
Lemma lem1151063 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term189 _27073 P h x t) = (term189 _27073 P h x t).
Proof. exact (eq_refl (term189 _27073 P h x t)). Qed.
Lemma lem1151072 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : ((term62 _27073 x P t) = (term78 _27073 P x t)) = ((term62 _27073 x P t) = (term78 _27073 P x t)).
Proof. exact (eq_refl ((term62 _27073 x P t) = (term78 _27073 P x t))). Qed.
Lemma lem1151073 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term114 _27073 P t) = (term114 _27073 P t).
Proof. exact (fun_ext (fun x : _27073 => @lem1151072 _27073 P x t)). Qed.
Lemma lem1151074 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1151075 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term8 _27073 P t) = (term8 _27073 P t).
Proof. exact (MK_COMB (@lem1151074 _27073) (@lem1151073 _27073 P t)). Qed.
Lemma lem1151076 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1151077 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) : (term10 _27073 P t) = (term10 _27073 P t).
Proof. exact (MK_COMB (@lem1151076) (@lem1151075 _27073 P t)). Qed.
Lemma lem1151078 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term190 _27073 P h x t) = (term190 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151077 _27073 P t) (@lem1151063 _27073 P h x t)). Qed.
Lemma lem1151079 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term192 _27073 h x t) = (term192 _27073 h x t).
Proof. exact (fun_ext (fun P : _27073 -> Prop => @lem1151078 _27073 P h x t)). Qed.
Lemma lem1151080 {_27073 : Type'} : (@all (_27073 -> Prop)) = (@all (_27073 -> Prop)).
Proof. exact (eq_refl (@all (_27073 -> Prop))). Qed.
Lemma lem1151081 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term194 _27073 h x t) = (term194 _27073 h x t).
Proof. exact (MK_COMB (@lem1151080 _27073) (@lem1151079 _27073 h x t)). Qed.
Lemma lem1151082 {_27073 : Type'} (x : _27073) (t : list _27073) : (term196 _27073 x t) = (term196 _27073 x t).
Proof. exact (fun_ext (fun h : _27073 => @lem1151081 _27073 h x t)). Qed.
Lemma lem1151083 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1151084 {_27073 : Type'} (x : _27073) (t : list _27073) : (term198 _27073 x t) = (term198 _27073 x t).
Proof. exact (MK_COMB (@lem1151083 _27073) (@lem1151082 _27073 x t)). Qed.
Lemma lem1151085 {_27073 : Type'} (t : list _27073) : (term200 _27073 t) = (term200 _27073 t).
Proof. exact (fun_ext (fun x : _27073 => @lem1151084 _27073 x t)). Qed.
Lemma lem1151086 {_27073 : Type'} : (@all _27073) = (@all _27073).
Proof. exact (eq_refl (@all _27073)). Qed.
Lemma lem1151087 {_27073 : Type'} (t : list _27073) : (term202 _27073 t) = (term202 _27073 t).
Proof. exact (MK_COMB (@lem1151086 _27073) (@lem1151085 _27073 t)). Qed.
Lemma lem1151088 {_27073 : Type'} : (term204 _27073) = (term204 _27073).
Proof. exact (fun_ext (fun t : list _27073 => @lem1151087 _27073 t)). Qed.
Lemma lem1151089 {_27073 : Type'} : (@all (list _27073)) = (@all (list _27073)).
Proof. exact (eq_refl (@all (list _27073))). Qed.
Lemma lem1151090 {_27073 : Type'} : (term206 _27073) = (term206 _27073).
Proof. exact (MK_COMB (@lem1151089 _27073) (@lem1151088 _27073)). Qed.
Lemma lem1151135 {_27073 : Type'} : (term205 _27073) = (term206 _27073).
Proof. exact (TRANS (@lem1151040 _27073) (@lem1151090 _27073)). Qed.
Lemma lem1151136 {_27073 : Type'} : (term206 _27073) = (term205 _27073).
Proof. exact (SYM (@lem1151135 _27073)). Qed.
Lemma lem1151140 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1151141 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : ((term78 _27073 P x t) = (term49 _27073 P h x t)) = (term181 _27073 P h x t).
Proof. exact (@lem1151140 ((term78 _27073 P x t) = (term49 _27073 P h x t))). Qed.
Lemma lem1151142 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term181 _27073 P h x t) = ((term78 _27073 P x t) = (term49 _27073 P h x t)).
Proof. exact (SYM (@lem1151141 _27073 P h x t)). Qed.
Lemma lem1151143 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term182 _27073 P h x t) : term182 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1151304 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (h1 : term76 _27073 P h) : term76 _27073 P h.
Proof. exact (h1). Qed.
Lemma lem1151313 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term115 _27073 P x t) = (term116 _27073 P x t).
Proof. exact (@lem17045 (P x) (@List.In _27073 x t)). Qed.
Lemma lem1151327 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term121 _27073 h x t) = (term122 _27073 h x t).
Proof. exact (@lem17160 (x = h) (@List.In _27073 x t)). Qed.
Lemma lem1151332 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term123 _27073 P x) = (term123 _27073 P x).
Proof. exact (eq_refl (term123 _27073 P x)). Qed.
Lemma lem1151333 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term124 _27073 P h x t) = (term125 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151332 _27073 P x) (@lem1151327 _27073 h x t)). Qed.
Lemma lem1151334 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term126 _27073 P h x t) = (term124 _27073 P h x t).
Proof. exact (@lem17045 (P x) (term47 _27073 h x t)). Qed.
Lemma lem1151335 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term126 _27073 P h x t) = (term125 _27073 P h x t).
Proof. exact (TRANS (@lem1151334 _27073 P h x t) (@lem1151333 _27073 P h x t)). Qed.
Lemma lem1151338 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term49 _27073 P h x t) = (term49 _27073 P h x t).
Proof. exact (eq_refl (term49 _27073 P h x t)). Qed.
Lemma lem1151339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1151340 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term207 _27073 P x t) = (term208 _27073 P x t).
Proof. exact (MK_COMB (@lem1151339) (@lem1151313 _27073 P x t)). Qed.
Lemma lem1151341 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term209 _27073 P h x t) = (term210 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151340 _27073 P x t) (@lem1151338 _27073 P h x t)). Qed.
Lemma lem1151343 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term211 _27073 P x t) = (term211 _27073 P x t).
Proof. exact (eq_refl (term211 _27073 P x t)). Qed.
Lemma lem1151344 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term212 _27073 P h x t) = (term213 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151343 _27073 P x t) (@lem1151335 _27073 P h x t)). Qed.
Lemma lem1151345 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1151346 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term214 _27073 P h x t) = (term215 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151345) (@lem1151344 _27073 P h x t)). Qed.
Lemma lem1151347 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term216 _27073 P h x t) = (term217 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151346 _27073 P h x t) (@lem1151341 _27073 P h x t)). Qed.
Lemma lem1151348 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term182 _27073 P h x t) = (term216 _27073 P h x t).
Proof. exact (@lem17646 (term78 _27073 P x t) (term49 _27073 P h x t)). Qed.
Lemma lem1151353 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term182 _27073 P h x t) = (term217 _27073 P h x t).
Proof. exact (TRANS (@lem1151348 _27073 P h x t) (@lem1151347 _27073 P h x t)). Qed.
Lemma lem1151354 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term182 _27073 P h x t) : term217 _27073 P h x t.
Proof. exact (EQ_MP (@lem1151353 _27073 P h x t) (@lem1151143 _27073 P h x t h1)). Qed.
Lemma lem1151427 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1151432 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1151433 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1151432 _27073 Prop f x). Qed.
Lemma lem1151435 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (P h) = (@I (_27073 -> Prop) P h).
Proof. exact (@lem1151433 _27073 P h). Qed.
Lemma lem1151436 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term76 _27073 P h) = (term141 _27073 P h).
Proof. exact (MK_COMB (@lem1151427) (@lem1151435 _27073 P h)). Qed.
Lemma lem1151450 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term47 _27073 h x t) = (term47 _27073 h x t).
Proof. exact (eq_refl (term47 _27073 h x t)). Qed.
Lemma lem1151455 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1151456 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1151455 _27073 Prop f x). Qed.
Lemma lem1151458 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1151456 _27073 P x). Qed.
Lemma lem1151459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1151460 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term33 _27073 P x) = (term138 _27073 P x).
Proof. exact (MK_COMB (@lem1151459) (@lem1151458 _27073 P x)). Qed.
Lemma lem1151461 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term49 _27073 P h x t) = (term139 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151460 _27073 P x) (@lem1151450 _27073 h x t)). Qed.
Lemma lem1151468 {_27073 : Type'} (x : _27073) (t : list _27073) : (term140 _27073 x t) = (term140 _27073 x t).
Proof. exact (eq_refl (term140 _27073 x t)). Qed.
Lemma lem1151469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1151474 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1151475 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1151474 _27073 Prop f x). Qed.
Lemma lem1151477 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1151475 _27073 P x). Qed.
Lemma lem1151478 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term76 _27073 P x) = (term141 _27073 P x).
Proof. exact (MK_COMB (@lem1151469) (@lem1151477 _27073 P x)). Qed.
Lemma lem1151479 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1151480 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term123 _27073 P x) = (term142 _27073 P x).
Proof. exact (MK_COMB (@lem1151479) (@lem1151478 _27073 P x)). Qed.
Lemma lem1151481 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term116 _27073 P x t) = (term143 _27073 P x t).
Proof. exact (MK_COMB (@lem1151480 _27073 P x) (@lem1151468 _27073 x t)). Qed.
Lemma lem1151482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1151483 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term208 _27073 P x t) = (term218 _27073 P x t).
Proof. exact (MK_COMB (@lem1151482) (@lem1151481 _27073 P x t)). Qed.
Lemma lem1151484 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term210 _27073 P h x t) = (term219 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151483 _27073 P x t) (@lem1151461 _27073 P h x t)). Qed.
Lemma lem1151501 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term122 _27073 h x t) = (term122 _27073 h x t).
Proof. exact (eq_refl (term122 _27073 h x t)). Qed.
Lemma lem1151502 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1151507 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1151508 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1151507 _27073 Prop f x). Qed.
Lemma lem1151510 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1151508 _27073 P x). Qed.
Lemma lem1151511 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term76 _27073 P x) = (term141 _27073 P x).
Proof. exact (MK_COMB (@lem1151502) (@lem1151510 _27073 P x)). Qed.
Lemma lem1151512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1151513 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term123 _27073 P x) = (term142 _27073 P x).
Proof. exact (MK_COMB (@lem1151512) (@lem1151511 _27073 P x)). Qed.
Lemma lem1151514 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term125 _27073 P h x t) = (term147 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151513 _27073 P x) (@lem1151501 _27073 h x t)). Qed.
Lemma lem1151519 {_27073 : Type'} (x : _27073) (t : list _27073) : (@List.In _27073 x t) = (@List.In _27073 x t).
Proof. exact (eq_refl (@List.In _27073 x t)). Qed.
Lemma lem1151524 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1151525 {_27073 : Type'} (f : _27073 -> Prop) (x : _27073) : (f x) = (@I (_27073 -> Prop) f x).
Proof. exact (@lem1151524 _27073 Prop f x). Qed.
Lemma lem1151527 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1151525 _27073 P x). Qed.
Lemma lem1151528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1151529 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term33 _27073 P x) = (term138 _27073 P x).
Proof. exact (MK_COMB (@lem1151528) (@lem1151527 _27073 P x)). Qed.
Lemma lem1151530 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term78 _27073 P x t) = (term148 _27073 P x t).
Proof. exact (MK_COMB (@lem1151529 _27073 P x) (@lem1151519 _27073 x t)). Qed.
Lemma lem1151531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1151532 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (t : list _27073) : (term211 _27073 P x t) = (term220 _27073 P x t).
Proof. exact (MK_COMB (@lem1151531) (@lem1151530 _27073 P x t)). Qed.
Lemma lem1151533 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term213 _27073 P h x t) = (term221 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151532 _27073 P x t) (@lem1151514 _27073 P h x t)). Qed.
Lemma lem1151534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1151535 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term215 _27073 P h x t) = (term222 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151534) (@lem1151533 _27073 P h x t)). Qed.
Lemma lem1151536 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term217 _27073 P h x t) = (term223 _27073 P h x t).
Proof. exact (MK_COMB (@lem1151535 _27073 P h x t) (@lem1151484 _27073 P h x t)). Qed.
Lemma lem1151537 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term182 _27073 P h x t) : term223 _27073 P h x t.
Proof. exact (EQ_MP (@lem1151536 _27073 P h x t) (@lem1151354 _27073 P h x t h1)). Qed.
Lemma lem1151540 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : term221 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1151541 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) : term219 _27073 P h x t.
Proof. exact (h1). Qed.
Lemma lem1151542 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : term147 _27073 P h x t.
Proof. exact (proj2 (@lem1151540 _27073 P h x t h1)). Qed.
Lemma lem1151543 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : term148 _27073 P x t.
Proof. exact (proj1 (@lem1151540 _27073 P h x t h1)). Qed.
Lemma lem1151547 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) : term122 _27073 h x t.
Proof. exact (h1). Qed.
Lemma lem1151550 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) : term139 _27073 P h x t.
Proof. exact (proj2 (@lem1151541 _27073 P h x t h1)). Qed.
Lemma lem1151551 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) : term143 _27073 P x t.
Proof. exact (proj1 (@lem1151541 _27073 P h x t h1)). Qed.
Lemma lem1151552 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) : term47 _27073 h x t.
Proof. exact (proj2 (@lem1151550 _27073 P h x t h1)). Qed.
Lemma lem1151617 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1151733 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1151737 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1151791 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1151853 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1151907 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : @List.In _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1151911 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) : term140 _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1151977 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1152009 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) : term140 _27073 x t.
Proof. exact (proj2 (@lem1151547 _27073 h x t h1)). Qed.
Lemma lem1152035 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) : @I (_27073 -> Prop) P x.
Proof. exact (proj1 (@lem1151550 _27073 P h x t h1)). Qed.
Lemma lem1152037 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1152039 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1152065 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) : @I (_27073 -> Prop) P x.
Proof. exact (proj1 (@lem1151550 _27073 P h x t h1)). Qed.
Lemma lem1152067 {_27073 : Type'} (x : _27073) (h : _27073) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1152099 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term141 _27073 P x.
Proof. exact (h1). Qed.
Lemma lem1152127 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : @List.In _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1152129 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) : term140 _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1152184 {_27073 : Type'} (P : _27073 -> Prop) : (term165 _27073 P) = (term165 _27073 P).
Proof. exact (eq_refl (term165 _27073 P)). Qed.
Lemma lem1152185 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (term166 _27073 P x) = (term166 _27073 P h).
Proof. exact (MK_COMB (@lem1152184 _27073 P) (@lem1152037 _27073 x h h1)). Qed.
Lemma lem1152186 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term166 _27073 P h) = (@I (_27073 -> Prop) P h).
Proof. exact (eq_refl (term166 _27073 P h)). Qed.
Lemma lem1152187 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term167 _27073 P x) = (term167 _27073 P x).
Proof. exact (eq_refl (term167 _27073 P x)). Qed.
Lemma lem1152188 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term166 _27073 P x) = (term166 _27073 P h)) = ((term166 _27073 P x) = (@I (_27073 -> Prop) P h)).
Proof. exact (MK_COMB (@lem1152187 _27073 P x) (@lem1152186 _27073 P h)). Qed.
Lemma lem1152189 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term166 _27073 P x) = (@I (_27073 -> Prop) P x).
Proof. exact (eq_refl (term166 _27073 P x)). Qed.
Lemma lem1152190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1152191 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term167 _27073 P x) = (term168 _27073 P x).
Proof. exact (MK_COMB (@lem1152190) (@lem1152189 _27073 P x)). Qed.
Lemma lem1152192 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (@I (_27073 -> Prop) P h) = (@I (_27073 -> Prop) P h).
Proof. exact (eq_refl (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1152193 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term166 _27073 P x) = (@I (_27073 -> Prop) P h)) = ((@I (_27073 -> Prop) P x) = (@I (_27073 -> Prop) P h)).
Proof. exact (MK_COMB (@lem1152191 _27073 P x) (@lem1152192 _27073 P h)). Qed.
Lemma lem1152194 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term166 _27073 P x) = (term166 _27073 P h)) = ((@I (_27073 -> Prop) P x) = (@I (_27073 -> Prop) P h)).
Proof. exact (TRANS (@lem1152188 _27073 x P h) (@lem1152193 _27073 x P h)). Qed.
Lemma lem1152195 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (@I (_27073 -> Prop) P x) = (@I (_27073 -> Prop) P h).
Proof. exact (EQ_MP (@lem1152194 _27073 x P h) (@lem1152185 _27073 P x h h1)). Qed.
Lemma lem1152197 {_27073 : Type'} (P : _27073 -> Prop) : (term155 _27073 P) = (term155 _27073 P).
Proof. exact (eq_refl (term155 _27073 P)). Qed.
Lemma lem1152198 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (term156 _27073 P x) = (term156 _27073 P h).
Proof. exact (MK_COMB (@lem1152197 _27073 P) (@lem1152037 _27073 x h h1)). Qed.
Lemma lem1152199 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term156 _27073 P h) = (term141 _27073 P h).
Proof. exact (eq_refl (term156 _27073 P h)). Qed.
Lemma lem1152200 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term157 _27073 P x) = (term157 _27073 P x).
Proof. exact (eq_refl (term157 _27073 P x)). Qed.
Lemma lem1152201 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term156 _27073 P x) = (term156 _27073 P h)) = ((term156 _27073 P x) = (term141 _27073 P h)).
Proof. exact (MK_COMB (@lem1152200 _27073 P x) (@lem1152199 _27073 P h)). Qed.
Lemma lem1152202 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term156 _27073 P x) = (term141 _27073 P x).
Proof. exact (eq_refl (term156 _27073 P x)). Qed.
Lemma lem1152203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1152204 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term157 _27073 P x) = (term158 _27073 P x).
Proof. exact (MK_COMB (@lem1152203) (@lem1152202 _27073 P x)). Qed.
Lemma lem1152205 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term141 _27073 P h) = (term141 _27073 P h).
Proof. exact (eq_refl (term141 _27073 P h)). Qed.
Lemma lem1152206 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term156 _27073 P x) = (term141 _27073 P h)) = ((term141 _27073 P x) = (term141 _27073 P h)).
Proof. exact (MK_COMB (@lem1152204 _27073 P x) (@lem1152205 _27073 P h)). Qed.
Lemma lem1152207 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term156 _27073 P x) = (term156 _27073 P h)) = ((term141 _27073 P x) = (term141 _27073 P h)).
Proof. exact (TRANS (@lem1152201 _27073 x P h) (@lem1152206 _27073 x P h)). Qed.
Lemma lem1152208 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (term141 _27073 P x) = (term141 _27073 P h).
Proof. exact (EQ_MP (@lem1152207 _27073 x P h) (@lem1152198 _27073 P x h h1)). Qed.
Lemma lem1152209 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : x = h) : term141 _27073 P h.
Proof. exact (EQ_MP (@lem1152208 _27073 P x h h2) (@lem1152039 _27073 P x h1)). Qed.
Lemma lem1152265 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (h1 : term76 _27073 P h) : term141 _27073 P h.
Proof. exact (EQ_MP (@lem1151436 _27073 P h) (@lem1151304 _27073 P h h1)). Qed.
Lemma lem1152280 {_27073 : Type'} (P : _27073 -> Prop) : (term165 _27073 P) = (term165 _27073 P).
Proof. exact (eq_refl (term165 _27073 P)). Qed.
Lemma lem1152281 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (term166 _27073 P x) = (term166 _27073 P h).
Proof. exact (MK_COMB (@lem1152280 _27073 P) (@lem1152067 _27073 x h h1)). Qed.
Lemma lem1152282 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term166 _27073 P h) = (@I (_27073 -> Prop) P h).
Proof. exact (eq_refl (term166 _27073 P h)). Qed.
Lemma lem1152283 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term167 _27073 P x) = (term167 _27073 P x).
Proof. exact (eq_refl (term167 _27073 P x)). Qed.
Lemma lem1152284 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term166 _27073 P x) = (term166 _27073 P h)) = ((term166 _27073 P x) = (@I (_27073 -> Prop) P h)).
Proof. exact (MK_COMB (@lem1152283 _27073 P x) (@lem1152282 _27073 P h)). Qed.
Lemma lem1152285 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term166 _27073 P x) = (@I (_27073 -> Prop) P x).
Proof. exact (eq_refl (term166 _27073 P x)). Qed.
Lemma lem1152286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1152287 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term167 _27073 P x) = (term168 _27073 P x).
Proof. exact (MK_COMB (@lem1152286) (@lem1152285 _27073 P x)). Qed.
Lemma lem1152288 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (@I (_27073 -> Prop) P h) = (@I (_27073 -> Prop) P h).
Proof. exact (eq_refl (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1152289 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term166 _27073 P x) = (@I (_27073 -> Prop) P h)) = ((@I (_27073 -> Prop) P x) = (@I (_27073 -> Prop) P h)).
Proof. exact (MK_COMB (@lem1152287 _27073 P x) (@lem1152288 _27073 P h)). Qed.
Lemma lem1152290 {_27073 : Type'} (x : _27073) (P : _27073 -> Prop) (h : _27073) : ((term166 _27073 P x) = (term166 _27073 P h)) = ((@I (_27073 -> Prop) P x) = (@I (_27073 -> Prop) P h)).
Proof. exact (TRANS (@lem1152284 _27073 x P h) (@lem1152289 _27073 x P h)). Qed.
Lemma lem1152291 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : x = h) : (@I (_27073 -> Prop) P x) = (@I (_27073 -> Prop) P h).
Proof. exact (EQ_MP (@lem1152290 _27073 x P h) (@lem1152281 _27073 P x h h1)). Qed.
Lemma lem1152335 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : @I (_27073 -> Prop) P x.
Proof. exact (proj1 (@lem1151543 _27073 P h x t h1)). Qed.
Lemma lem1152336 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : term169 _27073 P x.
Proof. exact (fun h0 : term141 _27073 P x => @lem1152335 _27073 P h x t h1). Qed.
Lemma lem1152338 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152339 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term169 _27073 P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1152338 (@I (_27073 -> Prop) P x)). Qed.
Lemma lem1152340 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : @I (_27073 -> Prop) P x.
Proof. exact (EQ_MP (@lem1152339 _27073 P x) (@lem1152336 _27073 P h x t h1)). Qed.
Lemma lem1152343 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1152345 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term141 _27073 P x) = (term171 _27073 P x).
Proof. exact (@lem1152343 (@I (_27073 -> Prop) P x)). Qed.
Lemma lem1152348 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term171 _27073 P x.
Proof. exact (EQ_MP (@lem1152345 _27073 P x) (@lem1151977 _27073 P x h1)). Qed.
Lemma lem1152351 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term221 _27073 P h x t) : False.
Proof. exact (@lem1152348 _27073 P x h1 (@lem1152340 _27073 P h x t h2)). Qed.
Lemma lem1152352 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term221 _27073 P h x t) : term172.
Proof. exact (fun h0 : ~ False => @lem1152351 _27073 P h x t h1 h2). Qed.
Lemma lem1152354 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152355 : term172 = False.
Proof. exact (@lem1152354 False). Qed.
Lemma lem1152356 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term221 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152355) (@lem1152352 _27073 P h x t h1 h2)). Qed.
Lemma lem1152417 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : @List.In _27073 x t.
Proof. exact (proj2 (@lem1151543 _27073 P h x t h1)). Qed.
Lemma lem1152418 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : term175 _27073 x t.
Proof. exact (fun h0 : term140 _27073 x t => @lem1152417 _27073 P h x t h1). Qed.
Lemma lem1152420 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152421 {_27073 : Type'} (x : _27073) (t : list _27073) : (term175 _27073 x t) = (@List.In _27073 x t).
Proof. exact (@lem1152420 (@List.In _27073 x t)). Qed.
Lemma lem1152422 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : @List.In _27073 x t.
Proof. exact (EQ_MP (@lem1152421 _27073 x t) (@lem1152418 _27073 P h x t h1)). Qed.
Lemma lem1152425 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1152427 {_27073 : Type'} (x : _27073) (t : list _27073) : (term140 _27073 x t) = (term176 _27073 x t).
Proof. exact (@lem1152425 (@List.In _27073 x t)). Qed.
Lemma lem1152430 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) : term176 _27073 x t.
Proof. exact (EQ_MP (@lem1152427 _27073 x t) (@lem1152009 _27073 h x t h1)). Qed.
Lemma lem1152433 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) (h2 : term221 _27073 P h x t) : False.
Proof. exact (@lem1152430 _27073 h x t h1 (@lem1152422 _27073 P h x t h2)). Qed.
Lemma lem1152434 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) (h2 : term221 _27073 P h x t) : term172.
Proof. exact (fun h0 : ~ False => @lem1152433 _27073 P h x t h1 h2). Qed.
Lemma lem1152436 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152437 : term172 = False.
Proof. exact (@lem1152436 False). Qed.
Lemma lem1152438 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term122 _27073 h x t) (h2 : term221 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152437) (@lem1152434 _27073 P h x t h1 h2)). Qed.
Lemma lem1152440 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term219 _27073 P h x t) (h2 : x = h) : @I (_27073 -> Prop) P h.
Proof. exact (EQ_MP (@lem1152195 _27073 P x h h2) (@lem1152035 _27073 P h x t h1)). Qed.
Lemma lem1152441 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term219 _27073 P h x t) (h2 : x = h) : term169 _27073 P h.
Proof. exact (fun h0 : term141 _27073 P h => @lem1152440 _27073 P t x h h1 h2). Qed.
Lemma lem1152443 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152444 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term169 _27073 P h) = (@I (_27073 -> Prop) P h).
Proof. exact (@lem1152443 (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1152445 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term219 _27073 P h x t) (h2 : x = h) : @I (_27073 -> Prop) P h.
Proof. exact (EQ_MP (@lem1152444 _27073 P h) (@lem1152441 _27073 P t x h h1 h2)). Qed.
Lemma lem1152448 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1152450 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term141 _27073 P h) = (term171 _27073 P h).
Proof. exact (@lem1152448 (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1152453 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : x = h) : term171 _27073 P h.
Proof. exact (EQ_MP (@lem1152450 _27073 P h) (@lem1152209 _27073 P x h h1 h2)). Qed.
Lemma lem1152456 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (@lem1152453 _27073 P x h h1 h3 (@lem1152445 _27073 P t x h h2 h3)). Qed.
Lemma lem1152457 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : term172.
Proof. exact (fun h0 : ~ False => @lem1152456 _27073 P t x h h1 h2 h3). Qed.
Lemma lem1152459 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152460 : term172 = False.
Proof. exact (@lem1152459 False). Qed.
Lemma lem1152463 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term219 _27073 P h x t) (h2 : x = h) : @I (_27073 -> Prop) P h.
Proof. exact (EQ_MP (@lem1152291 _27073 P x h h2) (@lem1152065 _27073 P h x t h1)). Qed.
Lemma lem1152464 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term219 _27073 P h x t) (h2 : x = h) : term169 _27073 P h.
Proof. exact (fun h0 : term141 _27073 P h => @lem1152463 _27073 P t x h h1 h2). Qed.
Lemma lem1152466 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152467 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term169 _27073 P h) = (@I (_27073 -> Prop) P h).
Proof. exact (@lem1152466 (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1152468 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term219 _27073 P h x t) (h2 : x = h) : @I (_27073 -> Prop) P h.
Proof. exact (EQ_MP (@lem1152467 _27073 P h) (@lem1152464 _27073 P t x h h1 h2)). Qed.
Lemma lem1152471 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1152473 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : (term141 _27073 P h) = (term171 _27073 P h).
Proof. exact (@lem1152471 (@I (_27073 -> Prop) P h)). Qed.
Lemma lem1152476 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (h1 : term76 _27073 P h) : term171 _27073 P h.
Proof. exact (EQ_MP (@lem1152473 _27073 P h) (@lem1152265 _27073 P h h1)). Qed.
Lemma lem1152479 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (@lem1152476 _27073 P h h1 (@lem1152468 _27073 P t x h h2 h3)). Qed.
Lemma lem1152480 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : term172.
Proof. exact (fun h0 : ~ False => @lem1152479 _27073 P t x h h1 h2 h3). Qed.
Lemma lem1152482 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152483 : term172 = False.
Proof. exact (@lem1152482 False). Qed.
Lemma lem1152486 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) : @I (_27073 -> Prop) P x.
Proof. exact (proj1 (@lem1151550 _27073 P h x t h1)). Qed.
Lemma lem1152487 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) : term169 _27073 P x.
Proof. exact (fun h0 : term141 _27073 P x => @lem1152486 _27073 P h x t h1). Qed.
Lemma lem1152489 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152490 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term169 _27073 P x) = (@I (_27073 -> Prop) P x).
Proof. exact (@lem1152489 (@I (_27073 -> Prop) P x)). Qed.
Lemma lem1152491 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) : @I (_27073 -> Prop) P x.
Proof. exact (EQ_MP (@lem1152490 _27073 P x) (@lem1152487 _27073 P h x t h1)). Qed.
Lemma lem1152494 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1152496 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) : (term141 _27073 P x) = (term171 _27073 P x).
Proof. exact (@lem1152494 (@I (_27073 -> Prop) P x)). Qed.
Lemma lem1152499 {_27073 : Type'} (P : _27073 -> Prop) (x : _27073) (h1 : term141 _27073 P x) : term171 _27073 P x.
Proof. exact (EQ_MP (@lem1152496 _27073 P x) (@lem1152099 _27073 P x h1)). Qed.
Lemma lem1152502 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) : False.
Proof. exact (@lem1152499 _27073 P x h1 (@lem1152491 _27073 P h x t h2)). Qed.
Lemma lem1152503 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) : term172.
Proof. exact (fun h0 : ~ False => @lem1152502 _27073 P h x t h1 h2). Qed.
Lemma lem1152505 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152506 : term172 = False.
Proof. exact (@lem1152505 False). Qed.
Lemma lem1152507 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152506) (@lem1152503 _27073 P h x t h1 h2)). Qed.
Lemma lem1152509 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : @List.In _27073 x t.
Proof. exact (h1). Qed.
Lemma lem1152510 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : term175 _27073 x t.
Proof. exact (fun h0 : term140 _27073 x t => @lem1152509 _27073 x t h1). Qed.
Lemma lem1152512 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152513 {_27073 : Type'} (x : _27073) (t : list _27073) : (term175 _27073 x t) = (@List.In _27073 x t).
Proof. exact (@lem1152512 (@List.In _27073 x t)). Qed.
Lemma lem1152514 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : @List.In _27073 x t) : @List.In _27073 x t.
Proof. exact (EQ_MP (@lem1152513 _27073 x t) (@lem1152510 _27073 x t h1)). Qed.
Lemma lem1152517 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1152519 {_27073 : Type'} (x : _27073) (t : list _27073) : (term140 _27073 x t) = (term176 _27073 x t).
Proof. exact (@lem1152517 (@List.In _27073 x t)). Qed.
Lemma lem1152522 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) : term176 _27073 x t.
Proof. exact (EQ_MP (@lem1152519 _27073 x t) (@lem1152129 _27073 x t h1)). Qed.
Lemma lem1152525 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (@lem1152522 _27073 x t h1 (@lem1152514 _27073 x t h2)). Qed.
Lemma lem1152526 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : term172.
Proof. exact (fun h0 : ~ False => @lem1152525 _27073 x t h1 h2). Qed.
Lemma lem1152528 (p : Prop) : (term170 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1152529 : term172 = False.
Proof. exact (@lem1152528 False). Qed.
Lemma lem1152530 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1152529) (@lem1152526 _27073 x t h1 h2)). Qed.
Lemma lem1152531 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152483) (@lem1152480 _27073 P t x h h1 h2 h3)). Qed.
Lemma lem1152532 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152460) (@lem1152457 _27073 P t x h h1 h2 h3)). Qed.
Lemma lem1152533 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (term140 _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : term140 _27073 x t => @lem1152530 _27073 x t h1 h2) (fun h3 : False => @lem1152129 _27073 x t h1)). Qed.
Lemma lem1152534 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1152533 _27073 x t h1 h2) (@lem1152129 _27073 x t h1)). Qed.
Lemma lem1152535 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (@List.In _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _27073 x t => @lem1152534 _27073 x t h1 h2) (fun h3 : False => @lem1152127 _27073 x t h2)). Qed.
Lemma lem1152536 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1152535 _27073 x t h1 h2) (@lem1152127 _27073 x t h2)). Qed.
Lemma lem1152537 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1152507 _27073 P h x t h1 h2) (fun h3 : False => @lem1152099 _27073 P x h1)). Qed.
Lemma lem1152538 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152537 _27073 P h x t h1 h2) (@lem1152099 _27073 P x h1)). Qed.
Lemma lem1152539 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1152531 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1152067 _27073 x h h3)). Qed.
Lemma lem1152540 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152539 _27073 P t x h h1 h2 h3) (@lem1152067 _27073 x h h3)). Qed.
Lemma lem1152541 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h4 : term141 _27073 P x => @lem1152532 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1152039 _27073 P x h1)). Qed.
Lemma lem1152542 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152541 _27073 P t x h h1 h2 h3) (@lem1152039 _27073 P x h1)). Qed.
Lemma lem1152543 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1152542 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1152037 _27073 x h h3)). Qed.
Lemma lem1152544 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152543 _27073 P t x h h1 h2 h3) (@lem1152037 _27073 x h h3)). Qed.
Lemma lem1152545 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term221 _27073 P h x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1152356 _27073 P h x t h1 h2) (fun h3 : False => @lem1151977 _27073 P x h1)). Qed.
Lemma lem1152546 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term221 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152545 _27073 P h x t h1 h2) (@lem1151977 _27073 P x h1)). Qed.
Lemma lem1152547 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (term140 _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : term140 _27073 x t => @lem1152536 _27073 x t h1 h2) (fun h3 : False => @lem1151911 _27073 x t h1)). Qed.
Lemma lem1152548 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1152547 _27073 x t h1 h2) (@lem1151911 _27073 x t h1)). Qed.
Lemma lem1152549 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (@List.In _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _27073 x t => @lem1152548 _27073 x t h1 h2) (fun h3 : False => @lem1151907 _27073 x t h2)). Qed.
Lemma lem1152550 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1152549 _27073 x t h1 h2) (@lem1151907 _27073 x t h2)). Qed.
Lemma lem1152551 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1152538 _27073 P h x t h1 h2) (fun h3 : False => @lem1151853 _27073 P x h1)). Qed.
Lemma lem1152552 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152551 _27073 P h x t h1 h2) (@lem1151853 _27073 P x h1)). Qed.
Lemma lem1152553 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1152540 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1151791 _27073 x h h3)). Qed.
Lemma lem1152554 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152553 _27073 P t x h h1 h2 h3) (@lem1151791 _27073 x h h3)). Qed.
Lemma lem1152555 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h4 : term141 _27073 P x => @lem1152544 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1151737 _27073 P x h1)). Qed.
Lemma lem1152556 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152555 _27073 P t x h h1 h2 h3) (@lem1151737 _27073 P x h1)). Qed.
Lemma lem1152557 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1152556 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1151733 _27073 x h h3)). Qed.
Lemma lem1152558 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152557 _27073 P t x h h1 h2 h3) (@lem1151733 _27073 x h h3)). Qed.
Lemma lem1152559 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term221 _27073 P h x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1152546 _27073 P h x t h1 h2) (fun h3 : False => @lem1151617 _27073 P x h1)). Qed.
Lemma lem1152560 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term221 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152559 _27073 P h x t h1 h2) (@lem1151617 _27073 P x h1)). Qed.
Lemma lem1152561 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (term140 _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : term140 _27073 x t => @lem1152550 _27073 x t h1 h2) (fun h3 : False => @lem1151911 _27073 x t h1)). Qed.
Lemma lem1152562 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1152561 _27073 x t h1 h2) (@lem1151911 _27073 x t h1)). Qed.
Lemma lem1152563 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : (@List.In _27073 x t) = False.
Proof. exact (prop_ext (fun h3 : @List.In _27073 x t => @lem1152562 _27073 x t h1 h2) (fun h3 : False => @lem1151907 _27073 x t h2)). Qed.
Lemma lem1152564 {_27073 : Type'} (x : _27073) (t : list _27073) (h1 : term140 _27073 x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (EQ_MP (@lem1152563 _27073 x t h1 h2) (@lem1151907 _27073 x t h2)). Qed.
Lemma lem1152565 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1152552 _27073 P h x t h1 h2) (fun h3 : False => @lem1151853 _27073 P x h1)). Qed.
Lemma lem1152566 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152565 _27073 P h x t h1 h2) (@lem1151853 _27073 P x h1)). Qed.
Lemma lem1152567 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1152554 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1151791 _27073 x h h3)). Qed.
Lemma lem1152568 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152567 _27073 P t x h h1 h2 h3) (@lem1151791 _27073 x h h3)). Qed.
Lemma lem1152569 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h4 : term141 _27073 P x => @lem1152558 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1151737 _27073 P x h1)). Qed.
Lemma lem1152570 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152569 _27073 P t x h h1 h2 h3) (@lem1151737 _27073 P x h1)). Qed.
Lemma lem1152571 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h4 : x = h => @lem1152570 _27073 P t x h h1 h2 h3) (fun h4 : False => @lem1151733 _27073 x h h3)). Qed.
Lemma lem1152572 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term141 _27073 P x) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (EQ_MP (@lem1152571 _27073 P t x h h1 h2 h3) (@lem1151733 _27073 x h h3)). Qed.
Lemma lem1152573 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term221 _27073 P h x t) : (term141 _27073 P x) = False.
Proof. exact (prop_ext (fun h3 : term141 _27073 P x => @lem1152560 _27073 P h x t h1 h2) (fun h3 : False => @lem1151617 _27073 P x h1)). Qed.
Lemma lem1152574 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term141 _27073 P x) (h2 : term221 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152573 _27073 P h x t h1 h2) (@lem1151617 _27073 P x h1)). Qed.
Lemma lem1152575 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term219 _27073 P h x t) (h2 : @List.In _27073 x t) : False.
Proof. exact (or_elim (@lem1151551 _27073 P h x t h1) (fun h0 : term141 _27073 P x => @lem1152566 _27073 P h x t h0 h1) (fun h0 : term140 _27073 x t => @lem1152564 _27073 x t h0 h2)). Qed.
Lemma lem1152576 {_27073 : Type'} (P : _27073 -> Prop) (t : list _27073) (x : _27073) (h : _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) (h3 : x = h) : False.
Proof. exact (or_elim (@lem1151551 _27073 P h x t h2) (fun h0 : term141 _27073 P x => @lem1152572 _27073 P t x h h0 h2 h3) (fun h0 : term140 _27073 x t => @lem1152568 _27073 P t x h h1 h2 h3)). Qed.
Lemma lem1152577 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term76 _27073 P h) (h2 : term219 _27073 P h x t) : False.
Proof. exact (or_elim (@lem1151552 _27073 P h x t h2) (fun h0 : x = h => @lem1152576 _27073 P t x h h1 h2 h0) (fun h0 : @List.In _27073 x t => @lem1152575 _27073 P h x t h2 h0)). Qed.
Lemma lem1152578 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term221 _27073 P h x t) : False.
Proof. exact (or_elim (@lem1151542 _27073 P h x t h1) (fun h0 : term141 _27073 P x => @lem1152574 _27073 P h x t h0 h1) (fun h0 : term122 _27073 h x t => @lem1152438 _27073 P h x t h0 h1)). Qed.
Lemma lem1152579 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term76 _27073 P h) (h2 : term182 _27073 P h x t) : False.
Proof. exact (or_elim (@lem1151537 _27073 P h x t h2) (fun h0 : term221 _27073 P h x t => @lem1152578 _27073 P h x t h0) (fun h0 : term219 _27073 P h x t => @lem1152577 _27073 P h x t h1 h0)). Qed.
Lemma lem1152580 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term76 _27073 P h) (h2 : term182 _27073 P h x t) : (term76 _27073 P h) = False.
Proof. exact (prop_ext (fun h3 : term76 _27073 P h => @lem1152579 _27073 P h x t h1 h2) (fun h3 : False => @lem1151304 _27073 P h h1)). Qed.
Lemma lem1152581 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term76 _27073 P h) (h2 : term182 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152580 _27073 P h x t h1 h2) (@lem1151304 _27073 P h h1)). Qed.
Lemma lem1152582 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term76 _27073 P h) (h2 : term182 _27073 P h x t) : (term182 _27073 P h x t) = False.
Proof. exact (prop_ext (fun h3 : term182 _27073 P h x t => @lem1152581 _27073 P h x t h1 h2) (fun h3 : False => @lem1151143 _27073 P h x t h2)). Qed.
Lemma lem1152583 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term76 _27073 P h) (h2 : term182 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152582 _27073 P h x t h1 h2) (@lem1151143 _27073 P h x t h2)). Qed.
Lemma lem1152584 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term76 _27073 P h) : term181 _27073 P h x t.
Proof. exact (fun h0 : term182 _27073 P h x t => @lem1152583 _27073 P h x t h1 h0). Qed.
Lemma lem1152585 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term76 _27073 P h) : (term78 _27073 P x t) = (term49 _27073 P h x t).
Proof. exact (EQ_MP (@lem1151142 _27073 P h x t) (@lem1152584 _27073 x t P h h1)). Qed.
Lemma lem1152586 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term189 _27073 P h x t.
Proof. exact (fun h0 : term76 _27073 P h => @lem1152585 _27073 x t P h h0). Qed.
Lemma lem1152587 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term190 _27073 P h x t.
Proof. exact (fun h0 : term8 _27073 P t => @lem1152586 _27073 P h x t). Qed.
Lemma lem1152592 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : term194 _27073 h x t.
Proof. exact (fun P : _27073 -> Prop => @lem1152587 _27073 P h x t). Qed.
Lemma lem1152597 {_27073 : Type'} (x : _27073) (t : list _27073) : term198 _27073 x t.
Proof. exact (fun h : _27073 => @lem1152592 _27073 h x t). Qed.
Lemma lem1152602 {_27073 : Type'} (t : list _27073) : term202 _27073 t.
Proof. exact (fun x : _27073 => @lem1152597 _27073 x t). Qed.
Lemma lem1152607 {_27073 : Type'} : term206 _27073.
Proof. exact (fun t : list _27073 => @lem1152602 _27073 t). Qed.
Lemma lem1152608 {_27073 : Type'} : term205 _27073.
Proof. exact (EQ_MP (@lem1151136 _27073) (@lem1152607 _27073)). Qed.
Lemma lem1152609 {_27073 : Type'} (t : list _27073) : term224 _27073 t.
Proof. exact (@lem1152608 _27073 t). Qed.
Lemma lem1152610 {_27073 : Type'} (t : list _27073) : (term224 _27073 t) = (term201 _27073 t).
Proof. exact (eq_refl (term224 _27073 t)). Qed.
Lemma lem1152611 {_27073 : Type'} (t : list _27073) : term201 _27073 t.
Proof. exact (EQ_MP (@lem1152610 _27073 t) (@lem1152609 _27073 t)). Qed.
Lemma lem1152612 {_27073 : Type'} (t : list _27073) (x : _27073) : term225 _27073 t x.
Proof. exact (@lem1152611 _27073 t x). Qed.
Lemma lem1152613 {_27073 : Type'} (x : _27073) (t : list _27073) : (term225 _27073 t x) = (term197 _27073 x t).
Proof. exact (eq_refl (term225 _27073 t x)). Qed.
Lemma lem1152614 {_27073 : Type'} (x : _27073) (t : list _27073) : term197 _27073 x t.
Proof. exact (EQ_MP (@lem1152613 _27073 x t) (@lem1152612 _27073 t x)). Qed.
Lemma lem1152615 {_27073 : Type'} (x : _27073) (t : list _27073) (h : _27073) : term226 _27073 x t h.
Proof. exact (@lem1152614 _27073 x t h). Qed.
Lemma lem1152616 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : (term226 _27073 x t h) = (term193 _27073 h x t).
Proof. exact (eq_refl (term226 _27073 x t h)). Qed.
Lemma lem1152617 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) : term193 _27073 h x t.
Proof. exact (EQ_MP (@lem1152616 _27073 h x t) (@lem1152615 _27073 x t h)). Qed.
Lemma lem1152618 {_27073 : Type'} (h : _27073) (x : _27073) (t : list _27073) (P : _27073 -> Prop) : term227 _27073 h x t P.
Proof. exact (@lem1152617 _27073 h x t P). Qed.
Lemma lem1152619 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : (term227 _27073 h x t P) = (term183 _27073 P h x t).
Proof. exact (eq_refl (term227 _27073 h x t P)). Qed.
Lemma lem1152620 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term183 _27073 P h x t.
Proof. exact (EQ_MP (@lem1152619 _27073 P h x t) (@lem1152618 _27073 h x t P)). Qed.
Lemma lem1152622 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) : term183 _27073 P h x t.
Proof. exact (@lem1150961 _27073 P h x t (@lem1152620 _27073 P h x t)). Qed.
Lemma lem1152623 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term188 _27073 P h x t.
Proof. exact (@lem1152622 _27073 P h x t (@lem1148216 _27073 P t h1)). Qed.
Lemma lem1152624 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : term76 _27073 P h) : term181 _27073 P h x t.
Proof. exact (@lem1152623 _27073 h x P t h1 (@lem1148346 _27073 P h h2)). Qed.
Lemma lem1152625 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term8 _27073 P t) (h2 : term76 _27073 P h) (h3 : term182 _27073 P h x t) : False.
Proof. exact (@lem1152624 _27073 x t P h h1 h2 (@lem1150945 _27073 P h x t h3)). Qed.
Lemma lem1152626 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term8 _27073 P t) (h2 : term76 _27073 P h) (h3 : term182 _27073 P h x t) : (term182 _27073 P h x t) = False.
Proof. exact (prop_ext (fun h4 : term182 _27073 P h x t => @lem1152625 _27073 P h x t h1 h2 h3) (fun h4 : False => @lem1150945 _27073 P h x t h3)). Qed.
Lemma lem1152627 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (x : _27073) (t : list _27073) (h1 : term8 _27073 P t) (h2 : term76 _27073 P h) (h3 : term182 _27073 P h x t) : False.
Proof. exact (EQ_MP (@lem1152626 _27073 P h x t h1 h2 h3) (@lem1150945 _27073 P h x t h3)). Qed.
Lemma lem1152628 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : term76 _27073 P h) : term181 _27073 P h x t.
Proof. exact (fun h0 : term182 _27073 P h x t => @lem1152627 _27073 P h x t h1 h2 h0). Qed.
Lemma lem1152629 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : term76 _27073 P h) : (term78 _27073 P x t) = (term49 _27073 P h x t).
Proof. exact (EQ_MP (@lem1150944 _27073 P h x t) (@lem1152628 _27073 x t P h h1 h2)). Qed.
Lemma lem1152632 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : term76 _27073 P h) : (term62 _27073 x P t) = (term49 _27073 P h x t).
Proof. exact (EQ_MP (@lem1148429 _27073 h x P t h1) (@lem1152629 _27073 x t P h h1 h2)). Qed.
Lemma lem1152633 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : term76 _27073 P h) : (term76 _27073 P h) = ((term62 _27073 x P t) = (term49 _27073 P h x t)).
Proof. exact (prop_ext (fun h3 : term76 _27073 P h => @lem1152632 _27073 x t P h h1 h2) (fun h3 : (term62 _27073 x P t) = (term49 _27073 P h x t) => @lem1148346 _27073 P h h2)). Qed.
Lemma lem1152634 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : term76 _27073 P h) : (term62 _27073 x P t) = (term49 _27073 P h x t).
Proof. exact (EQ_MP (@lem1152633 _27073 x t P h h1 h2) (@lem1148346 _27073 P h h2)). Qed.
Lemma lem1152635 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term65 _27073 P h x t.
Proof. exact (fun h0 : term76 _27073 P h => @lem1152634 _27073 x t P h h1 h0). Qed.
Lemma lem1152636 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : P h) : (term67 _27073 x h P t) = (term49 _27073 P h x t).
Proof. exact (EQ_MP (@lem1148402 _27073 h x P t h1) (@lem1150940 _27073 x t P h h1 h2)). Qed.
Lemma lem1152637 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : P h) : (P h) = ((term67 _27073 x h P t) = (term49 _27073 P h x t)).
Proof. exact (prop_ext (fun h3 : P h => @lem1152636 _27073 x t P h h1 h2) (fun h3 : (term67 _27073 x h P t) = (term49 _27073 P h x t) => @lem1148329 _27073 P h h2)). Qed.
Lemma lem1152638 {_27073 : Type'} (x : _27073) (t : list _27073) (P : _27073 -> Prop) (h : _27073) (h1 : term8 _27073 P t) (h2 : P h) : (term67 _27073 x h P t) = (term49 _27073 P h x t).
Proof. exact (EQ_MP (@lem1152637 _27073 x t P h h1 h2) (@lem1148329 _27073 P h h2)). Qed.
Lemma lem1152639 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term70 _27073 P h x t.
Proof. exact (fun h0 : P h => @lem1152638 _27073 x t P h h1 h0). Qed.
Lemma lem1152640 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term73 _27073 P h x t.
Proof. exact (conj (@lem1152639 _27073 h x P t h1) (@lem1152635 _27073 h x P t h1)). Qed.
Lemma lem1152641 {_27073 : Type'} (h : _27073) (x : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : (term43 _27073 x h P t) = (term49 _27073 P h x t).
Proof. exact (EQ_MP (@lem1148328 _27073 P h x t) (@lem1152640 _27073 h x P t h1)). Qed.
Lemma lem1152646 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term52 _27073 P h t.
Proof. exact (fun x : _27073 => @lem1152641 _27073 h x P t h1). Qed.
Lemma lem1152647 {_27073 : Type'} (h : _27073) (P : _27073 -> Prop) (t : list _27073) (h1 : term8 _27073 P t) : term12 _27073 P h t.
Proof. exact (EQ_MP (@lem1148310 _27073 P h t) (@lem1152646 _27073 h P t h1)). Qed.
Lemma lem1152648 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) (t : list _27073) : term14 _27073 P h t.
Proof. exact (fun h0 : term8 _27073 P t => @lem1152647 _27073 h P t h0). Qed.
Lemma lem1152653 {_27073 : Type'} (P : _27073 -> Prop) (h : _27073) : term18 _27073 P h.
Proof. exact (fun t : list _27073 => @lem1152648 _27073 P h t). Qed.
Lemma lem1152658 {_27073 : Type'} (P : _27073 -> Prop) : term22 _27073 P.
Proof. exact (fun h : _27073 => @lem1152653 _27073 P h). Qed.
Lemma lem1152659 {_27073 : Type'} (P : _27073 -> Prop) : term24 _27073 P.
Proof. exact (conj (@lem1148266 _27073 P) (@lem1152658 _27073 P)). Qed.
Lemma lem1152660 {_27073 : Type'} (P : _27073 -> Prop) : term29 _27073 P.
Proof. exact (@lem1148215 _27073 P (@lem1152659 _27073 P)). Qed.
Lemma lem1152665 {_27073 : Type'} : term228 _27073.
Proof. exact (fun P : _27073 -> Prop => @lem1152660 _27073 P). Qed.
