Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import AND_ALL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm554_spec.
Require Import thm555_spec.
Require Import thm585_spec.
Require Import thm586_spec.
Require Import thm616_spec.
Require Import thm617_spec.
Lemma lem1133062 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (l : list _26720) (h1 : (term0 _26720 P Q l) = (term1 _26720 P Q l)) : (term0 _26720 P Q l) = (term1 _26720 P Q l).
Proof. exact (h1). Qed.
Lemma lem1133063 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (l : list _26720) (h1 : (term0 _26720 P Q l) = (term1 _26720 P Q l)) : (term1 _26720 P Q l) = (term0 _26720 P Q l).
Proof. exact (SYM (@lem1133062 _26720 P Q l h1)). Qed.
Lemma lem1133064 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (l : list _26720) (h1 : (term1 _26720 P Q l) = (term0 _26720 P Q l)) : (term1 _26720 P Q l) = (term0 _26720 P Q l).
Proof. exact (h1). Qed.
Lemma lem1133065 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (l : list _26720) (h1 : (term1 _26720 P Q l) = (term0 _26720 P Q l)) : (term0 _26720 P Q l) = (term1 _26720 P Q l).
Proof. exact (SYM (@lem1133064 _26720 P Q l h1)). Qed.
Lemma lem1133066 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (l : list _26720) : ((term0 _26720 P Q l) = (term1 _26720 P Q l)) = ((term1 _26720 P Q l) = (term0 _26720 P Q l)).
Proof. exact (prop_ext (fun h1 : (term0 _26720 P Q l) = (term1 _26720 P Q l) => @lem1133063 _26720 P Q l h1) (fun h1 : (term1 _26720 P Q l) = (term0 _26720 P Q l) => @lem1133065 _26720 P Q l h1)). Qed.
Lemma lem1133067 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term2 _26720 P Q) = (term3 _26720 P Q).
Proof. exact (fun_ext (fun l : list _26720 => @lem1133066 _26720 P Q l)). Qed.
Lemma lem1133068 {_26720 : Type'} : (@all (list _26720)) = (@all (list _26720)).
Proof. exact (eq_refl (@all (list _26720))). Qed.
Lemma lem1133069 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term4 _26720 P Q) = (term5 _26720 P Q).
Proof. exact (MK_COMB (@lem1133068 _26720) (@lem1133067 _26720 P Q)). Qed.
Lemma lem1133070 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term5 _26720 P Q) = (term4 _26720 P Q).
Proof. exact (SYM (@lem1133069 _26720 P Q)). Qed.
Lemma lem1133072 {A : Type'} (P : type1143 A) : term6 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1133073 {_26720 : Type'} (P : type1143 _26720) : term6 _26720 P.
Proof. exact (@lem1133072 _26720 P). Qed.
Lemma lem1133074 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : term7 _26720 P Q.
Proof. exact (@lem1133073 _26720 (term3 _26720 P Q)). Qed.
Lemma lem1133075 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term8 _26720 P Q) = ((term9 _26720 P Q) = (term10 _26720 P Q)).
Proof. exact (eq_refl (term8 _26720 P Q)). Qed.
Lemma lem1133076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133077 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term11 _26720 P Q) = (term12 _26720 P Q).
Proof. exact (MK_COMB (@lem1133076) (@lem1133075 _26720 P Q)). Qed.
Lemma lem1133078 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term13 _26720 P Q t) = ((term1 _26720 P Q t) = (term0 _26720 P Q t)).
Proof. exact (eq_refl (term13 _26720 P Q t)). Qed.
Lemma lem1133079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133080 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term14 _26720 P Q t) = (term15 _26720 P Q t).
Proof. exact (MK_COMB (@lem1133079) (@lem1133078 _26720 P Q t)). Qed.
Lemma lem1133081 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) (t : list _26720) : (term16 _26720 P Q h t) = ((term17 _26720 P Q h t) = (term18 _26720 P Q h t)).
Proof. exact (eq_refl (term16 _26720 P Q h t)). Qed.
Lemma lem1133082 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) (t : list _26720) : (term19 _26720 P Q h t) = (term20 _26720 P Q h t).
Proof. exact (MK_COMB (@lem1133080 _26720 P Q t) (@lem1133081 _26720 P Q h t)). Qed.
Lemma lem1133083 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term21 _26720 P Q h) = (term22 _26720 P Q h).
Proof. exact (fun_ext (fun t : list _26720 => @lem1133082 _26720 P Q h t)). Qed.
Lemma lem1133084 {_26720 : Type'} : (@all (list _26720)) = (@all (list _26720)).
Proof. exact (eq_refl (@all (list _26720))). Qed.
Lemma lem1133085 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term23 _26720 P Q h) = (term24 _26720 P Q h).
Proof. exact (MK_COMB (@lem1133084 _26720) (@lem1133083 _26720 P Q h)). Qed.
Lemma lem1133086 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term25 _26720 P Q) = (term26 _26720 P Q).
Proof. exact (fun_ext (fun h : _26720 => @lem1133085 _26720 P Q h)). Qed.
Lemma lem1133087 {_26720 : Type'} : (@all _26720) = (@all _26720).
Proof. exact (eq_refl (@all _26720)). Qed.
Lemma lem1133088 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term27 _26720 P Q) = (term28 _26720 P Q).
Proof. exact (MK_COMB (@lem1133087 _26720) (@lem1133086 _26720 P Q)). Qed.
Lemma lem1133089 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term29 _26720 P Q) = (term30 _26720 P Q).
Proof. exact (MK_COMB (@lem1133077 _26720 P Q) (@lem1133088 _26720 P Q)). Qed.
Lemma lem1133090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1133091 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term31 _26720 P Q) = (term32 _26720 P Q).
Proof. exact (MK_COMB (@lem1133090) (@lem1133089 _26720 P Q)). Qed.
Lemma lem1133092 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (l : list _26720) : (term13 _26720 P Q l) = ((term1 _26720 P Q l) = (term0 _26720 P Q l)).
Proof. exact (eq_refl (term13 _26720 P Q l)). Qed.
Lemma lem1133093 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term33 _26720 P Q) = (term3 _26720 P Q).
Proof. exact (fun_ext (fun l : list _26720 => @lem1133092 _26720 P Q l)). Qed.
Lemma lem1133094 {_26720 : Type'} : (@all (list _26720)) = (@all (list _26720)).
Proof. exact (eq_refl (@all (list _26720))). Qed.
Lemma lem1133095 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term34 _26720 P Q) = (term5 _26720 P Q).
Proof. exact (MK_COMB (@lem1133094 _26720) (@lem1133093 _26720 P Q)). Qed.
Lemma lem1133096 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term7 _26720 P Q) = (term35 _26720 P Q).
Proof. exact (MK_COMB (@lem1133091 _26720 P Q) (@lem1133095 _26720 P Q)). Qed.
Lemma lem1133097 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : term35 _26720 P Q.
Proof. exact (EQ_MP (@lem1133096 _26720 P Q) (@lem1133074 _26720 P Q)). Qed.
Lemma lem1133112 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1133113 {_26720 : Type'} (P : _26720 -> Prop) : (@List.Forall _26720 P (@nil _26720)) = True.
Proof. exact (@lem1133112 _26720 P). Qed.
Lemma lem1133114 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term9 _26720 P Q) = True.
Proof. exact (@lem1133113 _26720 (term36 _26720 P Q)). Qed.
Lemma lem1133115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1133116 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term37 _26720 P Q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1133115) (@lem1133114 _26720 P Q)). Qed.
Lemma lem1133125 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1133126 {_26720 : Type'} (P : _26720 -> Prop) : (@List.Forall _26720 P (@nil _26720)) = True.
Proof. exact (@lem1133125 _26720 P). Qed.
Lemma lem1133127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133128 {_26720 : Type'} (P : _26720 -> Prop) : (term38 _26720 P) = (and True).
Proof. exact (MK_COMB (@lem1133127) (@lem1133126 _26720 P)). Qed.
Lemma lem1133130 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1133131 {_26720 : Type'} (P : _26720 -> Prop) : (@List.Forall _26720 P (@nil _26720)) = True.
Proof. exact (@lem1133130 _26720 P). Qed.
Lemma lem1133132 {_26720 : Type'} (Q : _26720 -> Prop) : (@List.Forall _26720 Q (@nil _26720)) = True.
Proof. exact (@lem1133131 _26720 Q). Qed.
Lemma lem1133133 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term10 _26720 P Q) = (True /\ True).
Proof. exact (MK_COMB (@lem1133128 _26720 P) (@lem1133132 _26720 Q)). Qed.
Lemma lem1133135 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1133136 : (True /\ True) = True.
Proof. exact (@lem1133135 True). Qed.
Lemma lem1133137 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term10 _26720 P Q) = True.
Proof. exact (TRANS (@lem1133133 _26720 P Q) (@lem1133136)). Qed.
Lemma lem1133138 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : ((term9 _26720 P Q) = (term10 _26720 P Q)) = (True = True).
Proof. exact (MK_COMB (@lem1133116 _26720 P Q) (@lem1133137 _26720 P Q)). Qed.
Lemma lem1133140 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1133141 : (True = True) = True.
Proof. exact (@lem1133140 True). Qed.
Lemma lem1133142 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : ((term9 _26720 P Q) = (term10 _26720 P Q)) = True.
Proof. exact (TRANS (@lem1133138 _26720 P Q) (@lem1133141)). Qed.
Lemma lem1133143 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : True = ((term9 _26720 P Q) = (term10 _26720 P Q)).
Proof. exact (SYM (@lem1133142 _26720 P Q)). Qed.
Lemma lem1133144 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term9 _26720 P Q) = (term10 _26720 P Q).
Proof. exact (EQ_MP (@lem1133143 _26720 P Q) (@lem0)). Qed.
Lemma lem1133158 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term39 _25307 P h t) = (term40 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1133159 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (t : list _26720) : (term39 _26720 P h t) = (term40 _26720 h P t).
Proof. exact (@lem1133158 _26720 h P t). Qed.
Lemma lem1133160 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term17 _26720 P Q h t) = (term41 _26720 h P Q t).
Proof. exact (@lem1133159 _26720 h (term36 _26720 P Q) t). Qed.
Lemma lem1133166 (q : Prop) (p : Prop) : (p /\ q) = (q /\ p).
Proof. exact (EQ_MP (@lem555 q p) (@lem554 p q)). Qed.
Lemma lem1133167 {_26720 : Type'} (t : list _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term41 _26720 h P Q t) = (term42 _26720 t P Q h).
Proof. exact (@lem1133166 (term1 _26720 P Q t) (term43 _26720 P Q h)). Qed.
Lemma lem1133175 {_26720 : Type'} (t : list _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term17 _26720 P Q h t) = (term42 _26720 t P Q h).
Proof. exact (TRANS (@lem1133160 _26720 h P Q t) (@lem1133167 _26720 t P Q h)). Qed.
Lemma lem1133177 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : (term1 _26720 P Q t) = (term0 _26720 P Q t).
Proof. exact (h1). Qed.
Lemma lem1133178 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : (term1 _26720 P Q t) = (term0 _26720 P Q t).
Proof. exact (@lem1133177 _26720 P Q t h1). Qed.
Lemma lem1133186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133187 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : (term44 _26720 P Q t) = (term45 _26720 P Q t).
Proof. exact (MK_COMB (@lem1133186) (@lem1133178 _26720 P Q t h1)). Qed.
Lemma lem1133189 {A B : Type'} (f : A -> B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1133190 {_26720 : Type'} (f : _26720 -> Prop) (y : _26720) : (term47 _26720 f y) = (f y).
Proof. exact (@lem1133189 _26720 Prop f y). Qed.
Lemma lem1133191 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term48 _26720 P Q h) = (term43 _26720 P Q h).
Proof. exact (@lem1133190 _26720 (term36 _26720 P Q) h). Qed.
Lemma lem1133192 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (x : _26720) : (term43 _26720 P Q x) = (term49 _26720 P Q x).
Proof. exact (eq_refl (term43 _26720 P Q x)). Qed.
Lemma lem1133193 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : (term50 _26720 P Q) = (term36 _26720 P Q).
Proof. exact (fun_ext (fun x : _26720 => @lem1133192 _26720 P Q x)). Qed.
Lemma lem1133194 {_26720 : Type'} (h : _26720) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1133195 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term48 _26720 P Q h) = (term43 _26720 P Q h).
Proof. exact (MK_COMB (@lem1133193 _26720 P Q) (@lem1133194 _26720 h)). Qed.
Lemma lem1133196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1133197 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term51 _26720 P Q h) = (term52 _26720 P Q h).
Proof. exact (MK_COMB (@lem1133196) (@lem1133195 _26720 P Q h)). Qed.
Lemma lem1133198 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term43 _26720 P Q h) = (term49 _26720 P Q h).
Proof. exact (eq_refl (term43 _26720 P Q h)). Qed.
Lemma lem1133199 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : ((term48 _26720 P Q h) = (term43 _26720 P Q h)) = ((term43 _26720 P Q h) = (term49 _26720 P Q h)).
Proof. exact (MK_COMB (@lem1133197 _26720 P Q h) (@lem1133198 _26720 P Q h)). Qed.
Lemma lem1133200 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term43 _26720 P Q h) = (term49 _26720 P Q h).
Proof. exact (EQ_MP (@lem1133199 _26720 P Q h) (@lem1133191 _26720 P Q h)). Qed.
Lemma lem1133208 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : (term42 _26720 t P Q h) = (term53 _26720 t P Q h).
Proof. exact (MK_COMB (@lem1133187 _26720 P Q t h1) (@lem1133200 _26720 P Q h)). Qed.
Lemma lem1133210 (p : Prop) (q : Prop) (r : Prop) : (term54 p q r) = (term55 p q r).
Proof. exact (EQ_MP (@lem586 p q r) (@lem585 p q r)). Qed.
Lemma lem1133211 {_26720 : Type'} (t : list _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : (term53 _26720 t P Q h) = (term56 _26720 t P Q h).
Proof. exact (@lem1133210 (@List.Forall _26720 P t) (@List.Forall _26720 Q t) (term49 _26720 P Q h)). Qed.
Lemma lem1133227 (q : Prop) (p : Prop) (r : Prop) : (term55 p q r) = (term55 q p r).
Proof. exact (EQ_MP (@lem617 q p r) (@lem616 p q r)). Qed.
Lemma lem1133228 {_26720 : Type'} (P : _26720 -> Prop) (t : list _26720) (Q : _26720 -> Prop) (h : _26720) : (term57 _26720 t P Q h) = (term58 _26720 P t Q h).
Proof. exact (@lem1133227 (P h) (@List.Forall _26720 Q t) (Q h)). Qed.
Lemma lem1133246 (q : Prop) (p : Prop) : (p /\ q) = (q /\ p).
Proof. exact (EQ_MP (@lem555 q p) (@lem554 p q)). Qed.
Lemma lem1133247 {_26720 : Type'} (h : _26720) (Q : _26720 -> Prop) (t : list _26720) : (term59 _26720 t Q h) = (term40 _26720 h Q t).
Proof. exact (@lem1133246 (Q h) (@List.Forall _26720 Q t)). Qed.
Lemma lem1133255 {_26720 : Type'} (P : _26720 -> Prop) (h : _26720) : (term60 _26720 P h) = (term60 _26720 P h).
Proof. exact (eq_refl (term60 _26720 P h)). Qed.
Lemma lem1133256 {_26720 : Type'} (P : _26720 -> Prop) (h : _26720) (Q : _26720 -> Prop) (t : list _26720) : (term58 _26720 P t Q h) = (term61 _26720 P h Q t).
Proof. exact (MK_COMB (@lem1133255 _26720 P h) (@lem1133247 _26720 h Q t)). Qed.
Lemma lem1133269 {_26720 : Type'} (P : _26720 -> Prop) (h : _26720) (Q : _26720 -> Prop) (t : list _26720) : (term57 _26720 t P Q h) = (term61 _26720 P h Q t).
Proof. exact (TRANS (@lem1133228 _26720 P t Q h) (@lem1133256 _26720 P h Q t)). Qed.
Lemma lem1133270 {_26720 : Type'} (P : _26720 -> Prop) (t : list _26720) : (term62 _26720 P t) = (term62 _26720 P t).
Proof. exact (eq_refl (term62 _26720 P t)). Qed.
Lemma lem1133271 {_26720 : Type'} (P : _26720 -> Prop) (h : _26720) (Q : _26720 -> Prop) (t : list _26720) : (term56 _26720 t P Q h) = (term63 _26720 P h Q t).
Proof. exact (MK_COMB (@lem1133270 _26720 P t) (@lem1133269 _26720 P h Q t)). Qed.
Lemma lem1133275 (q : Prop) (p : Prop) (r : Prop) : (term55 p q r) = (term55 q p r).
Proof. exact (EQ_MP (@lem617 q p r) (@lem616 p q r)). Qed.
Lemma lem1133276 {_26720 : Type'} (P : _26720 -> Prop) (h : _26720) (Q : _26720 -> Prop) (t : list _26720) : (term63 _26720 P h Q t) = (term64 _26720 P h Q t).
Proof. exact (@lem1133275 (P h) (@List.Forall _26720 P t) (term40 _26720 h Q t)). Qed.
Lemma lem1133292 (q : Prop) (p : Prop) (r : Prop) : (term55 p q r) = (term55 q p r).
Proof. exact (EQ_MP (@lem617 q p r) (@lem616 p q r)). Qed.
Lemma lem1133293 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term65 _26720 P h Q t) = (term66 _26720 h P Q t).
Proof. exact (@lem1133292 (Q h) (@List.Forall _26720 P t) (@List.Forall _26720 Q t)). Qed.
Lemma lem1133313 {_26720 : Type'} (P : _26720 -> Prop) (h : _26720) : (term60 _26720 P h) = (term60 _26720 P h).
Proof. exact (eq_refl (term60 _26720 P h)). Qed.
Lemma lem1133314 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term64 _26720 P h Q t) = (term67 _26720 h P Q t).
Proof. exact (MK_COMB (@lem1133313 _26720 P h) (@lem1133293 _26720 h P Q t)). Qed.
Lemma lem1133327 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term63 _26720 P h Q t) = (term67 _26720 h P Q t).
Proof. exact (TRANS (@lem1133276 _26720 P h Q t) (@lem1133314 _26720 h P Q t)). Qed.
Lemma lem1133328 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term56 _26720 t P Q h) = (term67 _26720 h P Q t).
Proof. exact (TRANS (@lem1133271 _26720 P h Q t) (@lem1133327 _26720 h P Q t)). Qed.
Lemma lem1133329 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term53 _26720 t P Q h) = (term67 _26720 h P Q t).
Proof. exact (TRANS (@lem1133211 _26720 t P Q h) (@lem1133328 _26720 h P Q t)). Qed.
Lemma lem1133330 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : (term42 _26720 t P Q h) = (term67 _26720 h P Q t).
Proof. exact (TRANS (@lem1133208 _26720 h P Q t h1) (@lem1133329 _26720 h P Q t)). Qed.
Lemma lem1133331 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : (term17 _26720 P Q h t) = (term67 _26720 h P Q t).
Proof. exact (TRANS (@lem1133175 _26720 t P Q h) (@lem1133330 _26720 h P Q t h1)). Qed.
Lemma lem1133332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1133333 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : (term68 _26720 P Q h t) = (term69 _26720 h P Q t).
Proof. exact (MK_COMB (@lem1133332) (@lem1133331 _26720 h P Q t h1)). Qed.
Lemma lem1133342 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term39 _25307 P h t) = (term40 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1133343 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (t : list _26720) : (term39 _26720 P h t) = (term40 _26720 h P t).
Proof. exact (@lem1133342 _26720 h P t). Qed.
Lemma lem1133351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1133352 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (t : list _26720) : (term70 _26720 P h t) = (term71 _26720 h P t).
Proof. exact (MK_COMB (@lem1133351) (@lem1133343 _26720 h P t)). Qed.
Lemma lem1133354 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term39 _25307 P h t) = (term40 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1133355 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (t : list _26720) : (term39 _26720 P h t) = (term40 _26720 h P t).
Proof. exact (@lem1133354 _26720 h P t). Qed.
Lemma lem1133356 {_26720 : Type'} (h : _26720) (Q : _26720 -> Prop) (t : list _26720) : (term39 _26720 Q h t) = (term40 _26720 h Q t).
Proof. exact (@lem1133355 _26720 h Q t). Qed.
Lemma lem1133364 {_26720 : Type'} (P : _26720 -> Prop) (h : _26720) (Q : _26720 -> Prop) (t : list _26720) : (term18 _26720 P Q h t) = (term72 _26720 P h Q t).
Proof. exact (MK_COMB (@lem1133352 _26720 h P t) (@lem1133356 _26720 h Q t)). Qed.
Lemma lem1133366 (p : Prop) (q : Prop) (r : Prop) : (term54 p q r) = (term55 p q r).
Proof. exact (EQ_MP (@lem586 p q r) (@lem585 p q r)). Qed.
Lemma lem1133367 {_26720 : Type'} (P : _26720 -> Prop) (h : _26720) (Q : _26720 -> Prop) (t : list _26720) : (term72 _26720 P h Q t) = (term64 _26720 P h Q t).
Proof. exact (@lem1133366 (P h) (@List.Forall _26720 P t) (term40 _26720 h Q t)). Qed.
Lemma lem1133383 (q : Prop) (p : Prop) (r : Prop) : (term55 p q r) = (term55 q p r).
Proof. exact (EQ_MP (@lem617 q p r) (@lem616 p q r)). Qed.
Lemma lem1133384 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term65 _26720 P h Q t) = (term66 _26720 h P Q t).
Proof. exact (@lem1133383 (Q h) (@List.Forall _26720 P t) (@List.Forall _26720 Q t)). Qed.
Lemma lem1133404 {_26720 : Type'} (P : _26720 -> Prop) (h : _26720) : (term60 _26720 P h) = (term60 _26720 P h).
Proof. exact (eq_refl (term60 _26720 P h)). Qed.
Lemma lem1133405 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term64 _26720 P h Q t) = (term67 _26720 h P Q t).
Proof. exact (MK_COMB (@lem1133404 _26720 P h) (@lem1133384 _26720 h P Q t)). Qed.
Lemma lem1133418 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term72 _26720 P h Q t) = (term67 _26720 h P Q t).
Proof. exact (TRANS (@lem1133367 _26720 P h Q t) (@lem1133405 _26720 h P Q t)). Qed.
Lemma lem1133419 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : (term18 _26720 P Q h t) = (term67 _26720 h P Q t).
Proof. exact (TRANS (@lem1133364 _26720 P h Q t) (@lem1133418 _26720 h P Q t)). Qed.
Lemma lem1133420 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : ((term17 _26720 P Q h t) = (term18 _26720 P Q h t)) = ((term67 _26720 h P Q t) = (term67 _26720 h P Q t)).
Proof. exact (MK_COMB (@lem1133333 _26720 h P Q t h1) (@lem1133419 _26720 h P Q t)). Qed.
Lemma lem1133422 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1133423 (x : Prop) : (x = x) = True.
Proof. exact (@lem1133422 Prop x). Qed.
Lemma lem1133424 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) : ((term67 _26720 h P Q t) = (term67 _26720 h P Q t)) = True.
Proof. exact (@lem1133423 (term67 _26720 h P Q t)). Qed.
Lemma lem1133425 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : ((term17 _26720 P Q h t) = (term18 _26720 P Q h t)) = True.
Proof. exact (TRANS (@lem1133420 _26720 h P Q t h1) (@lem1133424 _26720 h P Q t)). Qed.
Lemma lem1133426 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : True = ((term17 _26720 P Q h t) = (term18 _26720 P Q h t)).
Proof. exact (SYM (@lem1133425 _26720 h P Q t h1)). Qed.
Lemma lem1133427 {_26720 : Type'} (h : _26720) (P : _26720 -> Prop) (Q : _26720 -> Prop) (t : list _26720) (h1 : (term1 _26720 P Q t) = (term0 _26720 P Q t)) : (term17 _26720 P Q h t) = (term18 _26720 P Q h t).
Proof. exact (EQ_MP (@lem1133426 _26720 h P Q t h1) (@lem0)). Qed.
Lemma lem1133428 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) (t : list _26720) : term20 _26720 P Q h t.
Proof. exact (fun h0 : (term1 _26720 P Q t) = (term0 _26720 P Q t) => @lem1133427 _26720 h P Q t h0). Qed.
Lemma lem1133433 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) (h : _26720) : term24 _26720 P Q h.
Proof. exact (fun t : list _26720 => @lem1133428 _26720 P Q h t). Qed.
Lemma lem1133438 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : term28 _26720 P Q.
Proof. exact (fun h : _26720 => @lem1133433 _26720 P Q h). Qed.
Lemma lem1133439 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : term30 _26720 P Q.
Proof. exact (conj (@lem1133144 _26720 P Q) (@lem1133438 _26720 P Q)). Qed.
Lemma lem1133440 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : term5 _26720 P Q.
Proof. exact (@lem1133097 _26720 P Q (@lem1133439 _26720 P Q)). Qed.
Lemma lem1133441 {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop) : term4 _26720 P Q.
Proof. exact (EQ_MP (@lem1133070 _26720 P Q) (@lem1133440 _26720 P Q)). Qed.
