Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_MAX_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import num_WOP_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10568_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Require Import thm89994_spec.
Lemma lem116995 (p : nat) (m : nat) : term0 p m.
Proof. exact (@lem9784 (p = (S m))). Qed.
Lemma lem116996 (p : nat) (m : nat) : (term0 p m) = (term1 p m).
Proof. exact (eq_refl (term0 p m)). Qed.
Lemma lem116997 (p : nat) (m : nat) : term1 p m.
Proof. exact (EQ_MP (@lem116996 p m) (@lem116995 p m)). Qed.
Lemma lem116999 (p : nat) (m : nat) (h1 : term2 p m) : term2 p m.
Proof. exact (h1). Qed.
Lemma lem117000 : term3.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem117001 (m : nat) : term4 m.
Proof. exact (@lem117000 m). Qed.
Lemma lem117002 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem117003 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem117002 m) (@lem117001 m)). Qed.
Lemma lem117004 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem117003 m n). Qed.
Lemma lem117005 (m : nat) (n : nat) : (term6 m n) = ((term7 m n) = (term8 m n)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem117011 : term9.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem117012 (m : nat) : term10 m.
Proof. exact (@lem117011 m). Qed.
Lemma lem117013 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem117014 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem117013 m) (@lem117012 m)). Qed.
Lemma lem117015 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem117014 m n). Qed.
Lemma lem117016 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem117029 : term15.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem117030 (m : nat) : term16 m.
Proof. exact (@lem117029 m). Qed.
Lemma lem117031 (m : nat) : (term16 m) = ((term17 m) = False).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem117040 : term18.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem117041 (m : nat) : term19 m.
Proof. exact (@lem117040 m). Qed.
Lemma lem117042 (m : nat) : (term19 m) = ((term20 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem117058 (a : Prop) : term21 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem117059 (a : Prop) : (term21 a) = (term22 a).
Proof. exact (eq_refl (term21 a)). Qed.
Lemma lem117060 (a : Prop) : term22 a.
Proof. exact (EQ_MP (@lem117059 a) (@lem117058 a)). Qed.
Lemma lem117061 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem117062 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem117077 (b : Prop) (c : Prop) : (term23 b c) = (term23 b c).
Proof. exact (eq_refl (term23 b c)). Qed.
Lemma lem117078 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term24 b c a) = (term25 b c).
Proof. exact (MK_COMB (@lem117077 b c) (@lem117061 a h1)). Qed.
Lemma lem117079 (b : Prop) (c : Prop) : (term25 b c) = ((term26 b c) = (term27 b c)).
Proof. exact (eq_refl (term25 b c)). Qed.
Lemma lem117080 (b : Prop) (c : Prop) (a : Prop) : (term28 b c a) = (term28 b c a).
Proof. exact (eq_refl (term28 b c a)). Qed.
Lemma lem117081 (a : Prop) (b : Prop) (c : Prop) : ((term24 b c a) = (term25 b c)) = ((term24 b c a) = ((term26 b c) = (term27 b c))).
Proof. exact (MK_COMB (@lem117080 b c a) (@lem117079 b c)). Qed.
Lemma lem117082 (a : Prop) (b : Prop) (c : Prop) : (term24 b c a) = ((term29 b c a) = (term30 a b c)).
Proof. exact (eq_refl (term24 b c a)). Qed.
Lemma lem117083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem117084 (a : Prop) (b : Prop) (c : Prop) : (term28 b c a) = (term31 a b c).
Proof. exact (MK_COMB (@lem117083) (@lem117082 a b c)). Qed.
Lemma lem117085 (b : Prop) (c : Prop) : ((term26 b c) = (term27 b c)) = ((term26 b c) = (term27 b c)).
Proof. exact (eq_refl ((term26 b c) = (term27 b c))). Qed.
Lemma lem117086 (a : Prop) (b : Prop) (c : Prop) : ((term24 b c a) = ((term26 b c) = (term27 b c))) = (((term29 b c a) = (term30 a b c)) = ((term26 b c) = (term27 b c))).
Proof. exact (MK_COMB (@lem117084 a b c) (@lem117085 b c)). Qed.
Lemma lem117087 (a : Prop) (b : Prop) (c : Prop) : ((term24 b c a) = (term25 b c)) = (((term29 b c a) = (term30 a b c)) = ((term26 b c) = (term27 b c))).
Proof. exact (TRANS (@lem117081 a b c) (@lem117086 a b c)). Qed.
Lemma lem117088 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term29 b c a) = (term30 a b c)) = ((term26 b c) = (term27 b c)).
Proof. exact (EQ_MP (@lem117087 a b c) (@lem117078 b c a h1)). Qed.
Lemma lem117089 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term26 b c) = (term27 b c)) = ((term29 b c a) = (term30 a b c)).
Proof. exact (SYM (@lem117088 b c a h1)). Qed.
Lemma lem117090 (b : Prop) (c : Prop) : (term23 b c) = (term23 b c).
Proof. exact (eq_refl (term23 b c)). Qed.
Lemma lem117091 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term24 b c a) = (term32 b c).
Proof. exact (MK_COMB (@lem117090 b c) (@lem117062 a h1)). Qed.
Lemma lem117092 (b : Prop) (c : Prop) : (term32 b c) = ((term33 b c) = (term34 b c)).
Proof. exact (eq_refl (term32 b c)). Qed.
Lemma lem117093 (b : Prop) (c : Prop) (a : Prop) : (term28 b c a) = (term28 b c a).
Proof. exact (eq_refl (term28 b c a)). Qed.
Lemma lem117094 (a : Prop) (b : Prop) (c : Prop) : ((term24 b c a) = (term32 b c)) = ((term24 b c a) = ((term33 b c) = (term34 b c))).
Proof. exact (MK_COMB (@lem117093 b c a) (@lem117092 b c)). Qed.
Lemma lem117095 (a : Prop) (b : Prop) (c : Prop) : (term24 b c a) = ((term29 b c a) = (term30 a b c)).
Proof. exact (eq_refl (term24 b c a)). Qed.
Lemma lem117096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem117097 (a : Prop) (b : Prop) (c : Prop) : (term28 b c a) = (term31 a b c).
Proof. exact (MK_COMB (@lem117096) (@lem117095 a b c)). Qed.
Lemma lem117098 (b : Prop) (c : Prop) : ((term33 b c) = (term34 b c)) = ((term33 b c) = (term34 b c)).
Proof. exact (eq_refl ((term33 b c) = (term34 b c))). Qed.
Lemma lem117099 (a : Prop) (b : Prop) (c : Prop) : ((term24 b c a) = ((term33 b c) = (term34 b c))) = (((term29 b c a) = (term30 a b c)) = ((term33 b c) = (term34 b c))).
Proof. exact (MK_COMB (@lem117097 a b c) (@lem117098 b c)). Qed.
Lemma lem117100 (a : Prop) (b : Prop) (c : Prop) : ((term24 b c a) = (term32 b c)) = (((term29 b c a) = (term30 a b c)) = ((term33 b c) = (term34 b c))).
Proof. exact (TRANS (@lem117094 a b c) (@lem117099 a b c)). Qed.
Lemma lem117101 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term29 b c a) = (term30 a b c)) = ((term33 b c) = (term34 b c)).
Proof. exact (EQ_MP (@lem117100 a b c) (@lem117091 b c a h1)). Qed.
Lemma lem117102 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term33 b c) = (term34 b c)) = ((term29 b c a) = (term30 a b c)).
Proof. exact (SYM (@lem117101 b c a h1)). Qed.
Lemma lem117108 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem117109 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem117108 b). Qed.
Lemma lem117110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117111 (b : Prop) : (term35 b) = (imp b).
Proof. exact (MK_COMB (@lem117110) (@lem117109 b)). Qed.
Lemma lem117113 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem117114 (c : Prop) : (c /\ True) = c.
Proof. exact (@lem117113 c). Qed.
Lemma lem117115 (b : Prop) (c : Prop) : (term26 b c) = (b -> c).
Proof. exact (MK_COMB (@lem117111 b) (@lem117114 c)). Qed.
Lemma lem117118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem117119 (b : Prop) (c : Prop) : (term36 b c) = (term37 b c).
Proof. exact (MK_COMB (@lem117118) (@lem117115 b c)). Qed.
Lemma lem117123 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem117124 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem117123 b). Qed.
Lemma lem117125 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117126 (b : Prop) : (term35 b) = (imp b).
Proof. exact (MK_COMB (@lem117125) (@lem117124 b)). Qed.
Lemma lem117127 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem117128 (b : Prop) (c : Prop) : (term27 b c) = (b -> c).
Proof. exact (MK_COMB (@lem117126 b) (@lem117127 c)). Qed.
Lemma lem117131 (b : Prop) (c : Prop) : ((term26 b c) = (term27 b c)) = ((b -> c) = (b -> c)).
Proof. exact (MK_COMB (@lem117119 b c) (@lem117128 b c)). Qed.
Lemma lem117133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem117134 (x : Prop) : (x = x) = True.
Proof. exact (@lem117133 Prop x). Qed.
Lemma lem117135 (b : Prop) (c : Prop) : ((b -> c) = (b -> c)) = True.
Proof. exact (@lem117134 (b -> c)). Qed.
Lemma lem117136 (b : Prop) (c : Prop) : ((term26 b c) = (term27 b c)) = True.
Proof. exact (TRANS (@lem117131 b c) (@lem117135 b c)). Qed.
Lemma lem117137 (b : Prop) (c : Prop) : True = ((term26 b c) = (term27 b c)).
Proof. exact (SYM (@lem117136 b c)). Qed.
Lemma lem117138 (b : Prop) (c : Prop) : (term26 b c) = (term27 b c).
Proof. exact (EQ_MP (@lem117137 b c) (@lem0)). Qed.
Lemma lem117144 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem117145 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem117144 b). Qed.
Lemma lem117146 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117147 (b : Prop) : (term38 b) = (imp False).
Proof. exact (MK_COMB (@lem117146) (@lem117145 b)). Qed.
Lemma lem117149 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem117150 (c : Prop) : (c /\ False) = False.
Proof. exact (@lem117149 c). Qed.
Lemma lem117151 (b : Prop) (c : Prop) : (term33 b c) = (False -> False).
Proof. exact (MK_COMB (@lem117147 b) (@lem117150 c)). Qed.
Lemma lem117153 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem117154 : (False -> False) = True.
Proof. exact (@lem117153 False). Qed.
Lemma lem117155 (b : Prop) (c : Prop) : (term33 b c) = True.
Proof. exact (TRANS (@lem117151 b c) (@lem117154)). Qed.
Lemma lem117156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem117157 (b : Prop) (c : Prop) : (term39 b c) = (@eq Prop True).
Proof. exact (MK_COMB (@lem117156) (@lem117155 b c)). Qed.
Lemma lem117161 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem117162 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem117161 b). Qed.
Lemma lem117163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117164 (b : Prop) : (term38 b) = (imp False).
Proof. exact (MK_COMB (@lem117163) (@lem117162 b)). Qed.
Lemma lem117165 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem117166 (b : Prop) (c : Prop) : (term34 b c) = (False -> c).
Proof. exact (MK_COMB (@lem117164 b) (@lem117165 c)). Qed.
Lemma lem117168 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem117169 (c : Prop) : (False -> c) = True.
Proof. exact (@lem117168 c). Qed.
Lemma lem117170 (b : Prop) (c : Prop) : (term34 b c) = True.
Proof. exact (TRANS (@lem117166 b c) (@lem117169 c)). Qed.
Lemma lem117171 (b : Prop) (c : Prop) : ((term33 b c) = (term34 b c)) = (True = True).
Proof. exact (MK_COMB (@lem117157 b c) (@lem117170 b c)). Qed.
Lemma lem117173 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem117174 : (True = True) = True.
Proof. exact (@lem117173 True). Qed.
Lemma lem117175 (b : Prop) (c : Prop) : ((term33 b c) = (term34 b c)) = True.
Proof. exact (TRANS (@lem117171 b c) (@lem117174)). Qed.
Lemma lem117176 (b : Prop) (c : Prop) : True = ((term33 b c) = (term34 b c)).
Proof. exact (SYM (@lem117175 b c)). Qed.
Lemma lem117177 (b : Prop) (c : Prop) : (term33 b c) = (term34 b c).
Proof. exact (EQ_MP (@lem117176 b c) (@lem0)). Qed.
Lemma lem117178 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term29 b c a) = (term30 a b c).
Proof. exact (EQ_MP (@lem117102 b c a h1) (@lem117177 b c)). Qed.
Lemma lem117179 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term29 b c a) = (term30 a b c).
Proof. exact (EQ_MP (@lem117089 b c a h1) (@lem117138 b c)). Qed.
Lemma lem117183 (P : nat -> Prop) : term40 P.
Proof. exact (@lem116994 P). Qed.
Lemma lem117184 (P : nat -> Prop) : (term40 P) = ((term41 P) = (term42 P)).
Proof. exact (eq_refl (term40 P)). Qed.
Lemma lem117186 (P : nat -> Prop) (h1 : term43 P) : term43 P.
Proof. exact (h1). Qed.
Lemma lem117187 (P : nat -> Prop) (h1 : term44 P) : term44 P.
Proof. exact (h1). Qed.
Lemma lem117188 (P : nat -> Prop) (h1 : term41 P) : term41 P.
Proof. exact (h1). Qed.
Lemma lem117189 (P : nat -> Prop) (a : nat) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem117190 (P : nat -> Prop) (h1 : term44 P) : term44 P.
Proof. exact (h1). Qed.
Lemma lem117196 (P : nat -> Prop) : (term41 P) = (term42 P).
Proof. exact (EQ_MP (@lem117184 P) (@lem117183 P)). Qed.
Lemma lem117197 (P : nat -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem117196 (term47 P)). Qed.
Lemma lem117198 (P : nat -> Prop) (M : nat) : (term48 P M) = (term49 P M).
Proof. exact (eq_refl (term48 P M)). Qed.
Lemma lem117199 (P : nat -> Prop) : (term50 P) = (term47 P).
Proof. exact (fun_ext (fun M : nat => @lem117198 P M)). Qed.
Lemma lem117200 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem117201 (P : nat -> Prop) : (term45 P) = (term44 P).
Proof. exact (MK_COMB (@lem117200) (@lem117199 P)). Qed.
Lemma lem117202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem117203 (P : nat -> Prop) : (term51 P) = (term52 P).
Proof. exact (MK_COMB (@lem117202) (@lem117201 P)). Qed.
Lemma lem117204 (P : nat -> Prop) (M : nat) : (term48 P M) = (term49 P M).
Proof. exact (eq_refl (term48 P M)). Qed.
Lemma lem117205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem117206 (P : nat -> Prop) (M : nat) : (term53 P M) = (term54 P M).
Proof. exact (MK_COMB (@lem117205) (@lem117204 P M)). Qed.
Lemma lem117207 (P : nat -> Prop) (m : nat) : (term48 P m) = (term49 P m).
Proof. exact (eq_refl (term48 P m)). Qed.
Lemma lem117208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem117209 (P : nat -> Prop) (m : nat) : (term55 P m) = (term56 P m).
Proof. exact (MK_COMB (@lem117208) (@lem117207 P m)). Qed.
Lemma lem117210 (m : nat) (M : nat) : (term57 m M) = (term57 m M).
Proof. exact (eq_refl (term57 m M)). Qed.
Lemma lem117211 (M : nat) (P : nat -> Prop) (m : nat) : (term58 M P m) = (term59 M P m).
Proof. exact (MK_COMB (@lem117210 m M) (@lem117209 P m)). Qed.
Lemma lem117212 (M : nat) (P : nat -> Prop) : (term60 M P) = (term61 M P).
Proof. exact (fun_ext (fun m : nat => @lem117211 M P m)). Qed.
Lemma lem117213 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117214 (M : nat) (P : nat -> Prop) : (term62 M P) = (term63 M P).
Proof. exact (MK_COMB (@lem117213) (@lem117212 M P)). Qed.
Lemma lem117215 (M : nat) (P : nat -> Prop) : (term64 M P) = (term65 M P).
Proof. exact (MK_COMB (@lem117206 P M) (@lem117214 M P)). Qed.
Lemma lem117216 (P : nat -> Prop) : (term66 P) = (term67 P).
Proof. exact (fun_ext (fun M : nat => @lem117215 M P)). Qed.
Lemma lem117217 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem117218 (P : nat -> Prop) : (term46 P) = (term68 P).
Proof. exact (MK_COMB (@lem117217) (@lem117216 P)). Qed.
Lemma lem117219 (P : nat -> Prop) : ((term45 P) = (term46 P)) = ((term44 P) = (term68 P)).
Proof. exact (MK_COMB (@lem117203 P) (@lem117218 P)). Qed.
Lemma lem117220 (P : nat -> Prop) : (term44 P) = (term68 P).
Proof. exact (EQ_MP (@lem117219 P) (@lem117197 P)). Qed.
Lemma lem117221 (P : nat -> Prop) (h1 : term44 P) : term68 P.
Proof. exact (EQ_MP (@lem117220 P) (@lem117190 P h1)). Qed.
Lemma lem117222 (m : nat) (P : nat -> Prop) (h1 : term65 m P) : term65 m P.
Proof. exact (h1). Qed.
Lemma lem117223 (m : nat) (P : nat -> Prop) (h1 : term65 m P) : term65 m P.
Proof. exact (h1). Qed.
Lemma lem117225 (a : Prop) (b : Prop) (c : Prop) : (term29 b c a) = (term30 a b c).
Proof. exact (or_elim (@lem117060 a) (fun h0 : a = True => @lem117179 b c a h0) (fun h0 : a = False => @lem117178 b c a h0)). Qed.
Lemma lem117226 (P : nat -> Prop) (m : nat) : (term69 P m) = (term70 P m).
Proof. exact (@lem117225 (term49 P m) (term63 m P) (P m)). Qed.
Lemma lem117249 (P : nat -> Prop) (m : nat) : (term70 P m) = (term69 P m).
Proof. exact (SYM (@lem117226 P m)). Qed.
Lemma lem117251 (P : nat -> Prop) : term71 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem117252 (P : nat -> Prop) : term72 P.
Proof. exact (@lem117251 (term73 P)). Qed.
Lemma lem117253 (P : nat -> Prop) : (term74 P) = (term75 P).
Proof. exact (eq_refl (term74 P)). Qed.
Lemma lem117254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem117255 (P : nat -> Prop) : (term76 P) = (term77 P).
Proof. exact (MK_COMB (@lem117254) (@lem117253 P)). Qed.
Lemma lem117256 (P : nat -> Prop) (m : nat) : (term78 P m) = (term70 P m).
Proof. exact (eq_refl (term78 P m)). Qed.
Lemma lem117257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117258 (P : nat -> Prop) (m : nat) : (term79 P m) = (term80 P m).
Proof. exact (MK_COMB (@lem117257) (@lem117256 P m)). Qed.
Lemma lem117259 (P : nat -> Prop) (m : nat) : (term81 P m) = (term82 P m).
Proof. exact (eq_refl (term81 P m)). Qed.
Lemma lem117260 (P : nat -> Prop) (m : nat) : (term83 P m) = (term84 P m).
Proof. exact (MK_COMB (@lem117258 P m) (@lem117259 P m)). Qed.
Lemma lem117261 (P : nat -> Prop) : (term85 P) = (term86 P).
Proof. exact (fun_ext (fun m : nat => @lem117260 P m)). Qed.
Lemma lem117262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117263 (P : nat -> Prop) : (term87 P) = (term88 P).
Proof. exact (MK_COMB (@lem117262) (@lem117261 P)). Qed.
Lemma lem117264 (P : nat -> Prop) : (term89 P) = (term90 P).
Proof. exact (MK_COMB (@lem117255 P) (@lem117263 P)). Qed.
Lemma lem117265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117266 (P : nat -> Prop) : (term91 P) = (term92 P).
Proof. exact (MK_COMB (@lem117265) (@lem117264 P)). Qed.
Lemma lem117267 (P : nat -> Prop) (m : nat) : (term78 P m) = (term70 P m).
Proof. exact (eq_refl (term78 P m)). Qed.
Lemma lem117268 (P : nat -> Prop) : (term93 P) = (term73 P).
Proof. exact (fun_ext (fun m : nat => @lem117267 P m)). Qed.
Lemma lem117269 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117270 (P : nat -> Prop) : (term94 P) = (term95 P).
Proof. exact (MK_COMB (@lem117269) (@lem117268 P)). Qed.
Lemma lem117271 (P : nat -> Prop) : (term72 P) = (term96 P).
Proof. exact (MK_COMB (@lem117266 P) (@lem117270 P)). Qed.
Lemma lem117272 (P : nat -> Prop) : term96 P.
Proof. exact (EQ_MP (@lem117271 P) (@lem117252 P)). Qed.
Lemma lem117285 (m : nat) : (term20 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem117042 m) (@lem117041 m)). Qed.
Lemma lem117286 (x : nat) : (term20 x) = (x = (NUMERAL 0)).
Proof. exact (@lem117285 x). Qed.
Lemma lem117289 (P : nat -> Prop) (x : nat) : (term97 P x) = (term97 P x).
Proof. exact (eq_refl (term97 P x)). Qed.
Lemma lem117290 (P : nat -> Prop) (x : nat) : (term98 P x) = (term99 P x).
Proof. exact (MK_COMB (@lem117289 P x) (@lem117286 x)). Qed.
Lemma lem117293 (P : nat -> Prop) : (term100 P) = (term101 P).
Proof. exact (fun_ext (fun x : nat => @lem117290 P x)). Qed.
Lemma lem117294 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117295 (P : nat -> Prop) : (term102 P) = (term103 P).
Proof. exact (MK_COMB (@lem117294) (@lem117293 P)). Qed.
Lemma lem117300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem117301 (P : nat -> Prop) : (term104 P) = (term105 P).
Proof. exact (MK_COMB (@lem117300) (@lem117295 P)). Qed.
Lemma lem117309 (m : nat) : (term17 m) = False.
Proof. exact (EQ_MP (@lem117031 m) (@lem117030 m)). Qed.
Lemma lem117310 (m' : nat) : (term17 m') = False.
Proof. exact (@lem117309 m'). Qed.
Lemma lem117311 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117312 (m' : nat) : (term106 m') = (imp False).
Proof. exact (MK_COMB (@lem117311) (@lem117310 m')). Qed.
Lemma lem117319 (P : nat -> Prop) (m' : nat) : (term56 P m') = (term56 P m').
Proof. exact (eq_refl (term56 P m')). Qed.
Lemma lem117320 (P : nat -> Prop) (m' : nat) : (term107 P m') = (term108 P m').
Proof. exact (MK_COMB (@lem117312 m') (@lem117319 P m')). Qed.
Lemma lem117322 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem117323 (P : nat -> Prop) (m' : nat) : (term108 P m') = True.
Proof. exact (@lem117322 (term56 P m')). Qed.
Lemma lem117324 (P : nat -> Prop) (m' : nat) : (term107 P m') = True.
Proof. exact (TRANS (@lem117320 P m') (@lem117323 P m')). Qed.
Lemma lem117325 (P : nat -> Prop) : (term109 P) = term110.
Proof. exact (fun_ext (fun m' : nat => @lem117324 P m')). Qed.
Lemma lem117326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117327 (P : nat -> Prop) : (term111 P) = term112.
Proof. exact (MK_COMB (@lem117326) (@lem117325 P)). Qed.
Lemma lem117329 {A : Type'} (t : Prop) : (term113 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem117330 (t : Prop) : (term114 t) = t.
Proof. exact (@lem117329 nat t). Qed.
Lemma lem117331 : term112 = True.
Proof. exact (@lem117330 True). Qed.
Lemma lem117332 (P : nat -> Prop) : (term111 P) = True.
Proof. exact (TRANS (@lem117327 P) (@lem117331)). Qed.
Lemma lem117333 (P : nat -> Prop) : (term115 P) = (term116 P).
Proof. exact (MK_COMB (@lem117301 P) (@lem117332 P)). Qed.
Lemma lem117335 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem117336 (P : nat -> Prop) : (term116 P) = (term103 P).
Proof. exact (@lem117335 (term103 P)). Qed.
Lemma lem117345 (P : nat -> Prop) : (term115 P) = (term103 P).
Proof. exact (TRANS (@lem117333 P) (@lem117336 P)). Qed.
Lemma lem117346 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117347 (P : nat -> Prop) : (term117 P) = (term118 P).
Proof. exact (MK_COMB (@lem117346) (@lem117345 P)). Qed.
Lemma lem117348 (P : nat -> Prop) : (term119 P) = (term119 P).
Proof. exact (eq_refl (term119 P)). Qed.
Lemma lem117349 (P : nat -> Prop) : (term75 P) = (term120 P).
Proof. exact (MK_COMB (@lem117347 P) (@lem117348 P)). Qed.
Lemma lem117352 (P : nat -> Prop) : (term120 P) = (term75 P).
Proof. exact (SYM (@lem117349 P)). Qed.
Lemma lem117353 (P : nat -> Prop) (h1 : term103 P) : term103 P.
Proof. exact (h1). Qed.
Lemma lem117354 (x : nat) (P : nat -> Prop) (h1 : term103 P) : term121 P x.
Proof. exact (@lem117353 P h1 x). Qed.
Lemma lem117355 (P : nat -> Prop) (x : nat) : (term121 P x) = (term99 P x).
Proof. exact (eq_refl (term121 P x)). Qed.
Lemma lem117358 (x : nat) (P : nat -> Prop) (h1 : term103 P) : term99 P x.
Proof. exact (EQ_MP (@lem117355 P x) (@lem117354 x P h1)). Qed.
Lemma lem117359 (a : nat) (P : nat -> Prop) (h1 : term103 P) : term99 P a.
Proof. exact (@lem117358 a P h1). Qed.
Lemma lem117360 (P : nat -> Prop) (a : nat) (h1 : term103 P) (h2 : P a) : a = (NUMERAL 0).
Proof. exact (@lem117359 a P h1 (@lem117189 P a h2)). Qed.
Lemma lem117375 (P : nat -> Prop) : (term122 P) = (term122 P).
Proof. exact (eq_refl (term122 P)). Qed.
Lemma lem117376 (P : nat -> Prop) (a : nat) (h1 : term103 P) (h2 : P a) : (term123 P a) = (term124 P).
Proof. exact (MK_COMB (@lem117375 P) (@lem117360 P a h1 h2)). Qed.
Lemma lem117377 (P : nat -> Prop) : (term124 P) = (term119 P).
Proof. exact (eq_refl (term124 P)). Qed.
Lemma lem117378 (P : nat -> Prop) (a : nat) : (term125 P a) = (term125 P a).
Proof. exact (eq_refl (term125 P a)). Qed.
Lemma lem117379 (a : nat) (P : nat -> Prop) : ((term123 P a) = (term124 P)) = ((term123 P a) = (term119 P)).
Proof. exact (MK_COMB (@lem117378 P a) (@lem117377 P)). Qed.
Lemma lem117380 (P : nat -> Prop) (a : nat) : (term123 P a) = (P a).
Proof. exact (eq_refl (term123 P a)). Qed.
Lemma lem117381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem117382 (P : nat -> Prop) (a : nat) : (term125 P a) = (term126 P a).
Proof. exact (MK_COMB (@lem117381) (@lem117380 P a)). Qed.
Lemma lem117383 (P : nat -> Prop) : (term119 P) = (term119 P).
Proof. exact (eq_refl (term119 P)). Qed.
Lemma lem117384 (a : nat) (P : nat -> Prop) : ((term123 P a) = (term119 P)) = ((P a) = (term119 P)).
Proof. exact (MK_COMB (@lem117382 P a) (@lem117383 P)). Qed.
Lemma lem117385 (a : nat) (P : nat -> Prop) : ((term123 P a) = (term124 P)) = ((P a) = (term119 P)).
Proof. exact (TRANS (@lem117379 a P) (@lem117384 a P)). Qed.
Lemma lem117386 (P : nat -> Prop) (a : nat) (h1 : term103 P) (h2 : P a) : (P a) = (term119 P).
Proof. exact (EQ_MP (@lem117385 a P) (@lem117376 P a h1 h2)). Qed.
Lemma lem117388 (P : nat -> Prop) (a : nat) (h1 : term103 P) (h2 : P a) : term119 P.
Proof. exact (EQ_MP (@lem117386 P a h1 h2) (@lem117189 P a h2)). Qed.
Lemma lem117389 (P : nat -> Prop) (a : nat) (h1 : P a) : term120 P.
Proof. exact (fun h0 : term103 P => @lem117388 P a h0 h1). Qed.
Lemma lem117390 (P : nat -> Prop) (a : nat) (h1 : P a) : term75 P.
Proof. exact (EQ_MP (@lem117352 P) (@lem117389 P a h1)). Qed.
Lemma lem117391 (m : nat) (P : nat -> Prop) (h1 : term127 m P) : term127 m P.
Proof. exact (h1). Qed.
Lemma lem117392 (m : nat) (P : nat -> Prop) (h1 : term128 m P) : term128 m P.
Proof. exact (h1). Qed.
Lemma lem117393 (m : nat) (P : nat -> Prop) (h1 : term128 m P) : term129 P m.
Proof. exact (@lem117392 m P h1 m). Qed.
Lemma lem117394 (P : nat -> Prop) (m : nat) : (term129 P m) = (term130 P m).
Proof. exact (eq_refl (term129 P m)). Qed.
Lemma lem117395 (m : nat) (P : nat -> Prop) (h1 : term128 m P) : term130 P m.
Proof. exact (EQ_MP (@lem117394 P m) (@lem117393 m P h1)). Qed.
Lemma lem117396 (P : nat -> Prop) (m : nat) (h1 : term131 P m) : term131 P m.
Proof. exact (h1). Qed.
Lemma lem117402 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem117016 m n) (@lem117015 m n)). Qed.
Lemma lem117403 (m : nat) : (term132 m) = (term133 m).
Proof. exact (@lem117402 m m). Qed.
Lemma lem117407 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem117408 (x : nat) : (x = x) = True.
Proof. exact (@lem117407 nat x). Qed.
Lemma lem117409 (m : nat) : (m = m) = True.
Proof. exact (@lem117408 m). Qed.
Lemma lem117410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem117411 (m : nat) : (term134 m) = (or True).
Proof. exact (MK_COMB (@lem117410) (@lem117409 m)). Qed.
Lemma lem117412 (m : nat) : (Peano.lt m m) = (Peano.lt m m).
Proof. exact (eq_refl (Peano.lt m m)). Qed.
Lemma lem117413 (m : nat) : (term133 m) = (term135 m).
Proof. exact (MK_COMB (@lem117411 m) (@lem117412 m)). Qed.
Lemma lem117415 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem117416 (m : nat) : (term135 m) = True.
Proof. exact (@lem117415 (Peano.lt m m)). Qed.
Lemma lem117417 (m : nat) : (term133 m) = True.
Proof. exact (TRANS (@lem117413 m) (@lem117416 m)). Qed.
Lemma lem117418 (m : nat) : (term132 m) = True.
Proof. exact (TRANS (@lem117403 m) (@lem117417 m)). Qed.
Lemma lem117419 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117420 (m : nat) : (term136 m) = (imp True).
Proof. exact (MK_COMB (@lem117419) (@lem117418 m)). Qed.
Lemma lem117427 (P : nat -> Prop) (m : nat) : (term56 P m) = (term56 P m).
Proof. exact (eq_refl (term56 P m)). Qed.
Lemma lem117428 (P : nat -> Prop) (m : nat) : (term130 P m) = (term137 P m).
Proof. exact (MK_COMB (@lem117420 m) (@lem117427 P m)). Qed.
Lemma lem117430 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem117431 (P : nat -> Prop) (m : nat) : (term137 P m) = (term56 P m).
Proof. exact (@lem117430 (term56 P m)). Qed.
Lemma lem117438 (P : nat -> Prop) (m : nat) : (term130 P m) = (term56 P m).
Proof. exact (TRANS (@lem117428 P m) (@lem117431 P m)). Qed.
Lemma lem117439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117440 (P : nat -> Prop) (m : nat) : (term138 P m) = (term139 P m).
Proof. exact (MK_COMB (@lem117439) (@lem117438 P m)). Qed.
Lemma lem117441 (P : nat -> Prop) (m : nat) : (term140 P m) = (term140 P m).
Proof. exact (eq_refl (term140 P m)). Qed.
Lemma lem117442 (P : nat -> Prop) (m : nat) : (term141 P m) = (term142 P m).
Proof. exact (MK_COMB (@lem117440 P m) (@lem117441 P m)). Qed.
Lemma lem117445 (P : nat -> Prop) (m : nat) : (term142 P m) = (term141 P m).
Proof. exact (SYM (@lem117442 P m)). Qed.
Lemma lem117446 (P : nat -> Prop) (m : nat) : (term142 P m) = (term143 P m).
Proof. exact (@lem10568 (term140 P m) (term56 P m)). Qed.
Lemma lem117447 (P : nat -> Prop) (m : nat) : (term143 P m) = (term142 P m).
Proof. exact (SYM (@lem117446 P m)). Qed.
Lemma lem117448 (P : nat -> Prop) (m : nat) (h1 : term144 P m) : term144 P m.
Proof. exact (h1). Qed.
Lemma lem117450 (t : Prop) : (term145 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem117451 (P : nat -> Prop) (m : nat) : (term146 P m) = (term49 P m).
Proof. exact (@lem117450 (term49 P m)). Qed.
Lemma lem117458 (P : nat -> Prop) (m : nat) : (term49 P m) = (term146 P m).
Proof. exact (SYM (@lem117451 P m)). Qed.
Lemma lem117459 (p : nat) (P : nat -> Prop) (m : nat) (h1 : term131 P m) : term147 P m p.
Proof. exact (@lem117396 P m h1 p). Qed.
Lemma lem117460 (P : nat -> Prop) (p : nat) (m : nat) : (term147 P m p) = (term148 P p m).
Proof. exact (eq_refl (term147 P m p)). Qed.
Lemma lem117461 (p : nat) (P : nat -> Prop) (m : nat) (h1 : term131 P m) : term148 P p m.
Proof. exact (EQ_MP (@lem117460 P p m) (@lem117459 p P m h1)). Qed.
Lemma lem117467 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem117005 m n) (@lem117004 m n)). Qed.
Lemma lem117468 (p : nat) (m : nat) : (term7 p m) = (term8 p m).
Proof. exact (@lem117467 p m). Qed.
Lemma lem117473 (P : nat -> Prop) (p : nat) : (term97 P p) = (term97 P p).
Proof. exact (eq_refl (term97 P p)). Qed.
Lemma lem117474 (P : nat -> Prop) (p : nat) (m : nat) : (term148 P p m) = (term149 P p m).
Proof. exact (MK_COMB (@lem117473 P p) (@lem117468 p m)). Qed.
Lemma lem117477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117478 (P : nat -> Prop) (p : nat) (m : nat) : (term150 P p m) = (term151 P p m).
Proof. exact (MK_COMB (@lem117477) (@lem117474 P p m)). Qed.
Lemma lem117481 (P : nat -> Prop) (p : nat) (m : nat) : (term152 P p m) = (term152 P p m).
Proof. exact (eq_refl (term152 P p m)). Qed.
Lemma lem117482 (P : nat -> Prop) (p : nat) (m : nat) : (term153 P p m) = (term154 P p m).
Proof. exact (MK_COMB (@lem117478 P p m) (@lem117481 P p m)). Qed.
Lemma lem117485 (P : nat -> Prop) (p : nat) (m : nat) : (term154 P p m) = (term153 P p m).
Proof. exact (SYM (@lem117482 P p m)). Qed.
Lemma lem117495 (P : nat -> Prop) (m : nat) : term155 P m.
Proof. exact (@lem82 (term140 P m)). Qed.
Lemma lem117502 (p : nat) (m : nat) (h1 : p = (S m)) : p = (S m).
Proof. exact (h1). Qed.
Lemma lem117503 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem117504 (P : nat -> Prop) (p : nat) (m : nat) (h1 : p = (S m)) : (P p) = (term140 P m).
Proof. exact (MK_COMB (@lem117503 P) (@lem117502 p m h1)). Qed.
Lemma lem117506 (P : nat -> Prop) (m : nat) (h1 : term144 P m) : (term140 P m) = False.
Proof. exact (@lem117495 P m (@lem117448 P m h1)). Qed.
Lemma lem117507 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (P p) = False.
Proof. exact (TRANS (@lem117504 P p m h2) (@lem117506 P m h1)). Qed.
Lemma lem117508 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117509 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (term97 P p) = (imp False).
Proof. exact (MK_COMB (@lem117508) (@lem117507 P p m h1 h2)). Qed.
Lemma lem117515 (p : nat) (m : nat) (h1 : p = (S m)) : p = (S m).
Proof. exact (h1). Qed.
Lemma lem117516 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem117517 (p : nat) (m : nat) (h1 : p = (S m)) : (@eq nat p) = (term156 m).
Proof. exact (MK_COMB (@lem117516) (@lem117515 p m h1)). Qed.
Lemma lem117518 (m : nat) : (S m) = (S m).
Proof. exact (eq_refl (S m)). Qed.
Lemma lem117519 (p : nat) (m : nat) (h1 : p = (S m)) : (p = (S m)) = ((S m) = (S m)).
Proof. exact (MK_COMB (@lem117517 p m h1) (@lem117518 m)). Qed.
Lemma lem117521 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem117522 (x : nat) : (x = x) = True.
Proof. exact (@lem117521 nat x). Qed.
Lemma lem117523 (m : nat) : ((S m) = (S m)) = True.
Proof. exact (@lem117522 (S m)). Qed.
Lemma lem117524 (p : nat) (m : nat) (h1 : p = (S m)) : (p = (S m)) = True.
Proof. exact (TRANS (@lem117519 p m h1) (@lem117523 m)). Qed.
Lemma lem117525 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem117526 (p : nat) (m : nat) (h1 : p = (S m)) : (term157 p m) = (or True).
Proof. exact (MK_COMB (@lem117525) (@lem117524 p m h1)). Qed.
Lemma lem117528 (p : nat) (m : nat) (h1 : p = (S m)) : p = (S m).
Proof. exact (h1). Qed.
Lemma lem117529 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem117530 (p : nat) (m : nat) (h1 : p = (S m)) : (Peano.le p) = (term158 m).
Proof. exact (MK_COMB (@lem117529) (@lem117528 p m h1)). Qed.
Lemma lem117531 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem117532 (p : nat) (m : nat) (h1 : p = (S m)) : (Peano.le p m) = (term159 m).
Proof. exact (MK_COMB (@lem117530 p m h1) (@lem117531 m)). Qed.
Lemma lem117533 (p : nat) (m : nat) (h1 : p = (S m)) : (term8 p m) = (term160 m).
Proof. exact (MK_COMB (@lem117526 p m h1) (@lem117532 p m h1)). Qed.
Lemma lem117535 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem117536 (m : nat) : (term160 m) = True.
Proof. exact (@lem117535 (term159 m)). Qed.
Lemma lem117537 (p : nat) (m : nat) (h1 : p = (S m)) : (term8 p m) = True.
Proof. exact (TRANS (@lem117533 p m h1) (@lem117536 m)). Qed.
Lemma lem117538 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (term149 P p m) = (False -> True).
Proof. exact (MK_COMB (@lem117509 P p m h1 h2) (@lem117537 p m h2)). Qed.
Lemma lem117540 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem117541 : (False -> True) = True.
Proof. exact (@lem117540 True). Qed.
Lemma lem117542 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (term149 P p m) = True.
Proof. exact (TRANS (@lem117538 P p m h1 h2) (@lem117541)). Qed.
Lemma lem117543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117544 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (term151 P p m) = (imp True).
Proof. exact (MK_COMB (@lem117543) (@lem117542 P p m h1 h2)). Qed.
Lemma lem117548 (p : nat) (m : nat) (h1 : p = (S m)) : p = (S m).
Proof. exact (h1). Qed.
Lemma lem117549 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem117550 (P : nat -> Prop) (p : nat) (m : nat) (h1 : p = (S m)) : (P p) = (term140 P m).
Proof. exact (MK_COMB (@lem117549 P) (@lem117548 p m h1)). Qed.
Lemma lem117552 (P : nat -> Prop) (m : nat) (h1 : term144 P m) : (term140 P m) = False.
Proof. exact (@lem117495 P m (@lem117448 P m h1)). Qed.
Lemma lem117553 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (P p) = False.
Proof. exact (TRANS (@lem117550 P p m h2) (@lem117552 P m h1)). Qed.
Lemma lem117554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117555 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (term97 P p) = (imp False).
Proof. exact (MK_COMB (@lem117554) (@lem117553 P p m h1 h2)). Qed.
Lemma lem117557 (p : nat) (m : nat) (h1 : p = (S m)) : p = (S m).
Proof. exact (h1). Qed.
Lemma lem117558 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem117559 (p : nat) (m : nat) (h1 : p = (S m)) : (Peano.le p) = (term158 m).
Proof. exact (MK_COMB (@lem117558) (@lem117557 p m h1)). Qed.
Lemma lem117560 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem117561 (p : nat) (m : nat) (h1 : p = (S m)) : (Peano.le p m) = (term159 m).
Proof. exact (MK_COMB (@lem117559 p m h1) (@lem117560 m)). Qed.
Lemma lem117562 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (term152 P p m) = (term161 m).
Proof. exact (MK_COMB (@lem117555 P p m h1 h2) (@lem117561 p m h2)). Qed.
Lemma lem117564 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem117565 (m : nat) : (term161 m) = True.
Proof. exact (@lem117564 (term159 m)). Qed.
Lemma lem117566 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (term152 P p m) = True.
Proof. exact (TRANS (@lem117562 P p m h1 h2) (@lem117565 m)). Qed.
Lemma lem117567 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (term154 P p m) = (True -> True).
Proof. exact (MK_COMB (@lem117544 P p m h1 h2) (@lem117566 P p m h1 h2)). Qed.
Lemma lem117569 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem117570 : (True -> True) = True.
Proof. exact (@lem117569 True). Qed.
Lemma lem117571 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : (term154 P p m) = True.
Proof. exact (TRANS (@lem117567 P p m h1 h2) (@lem117570)). Qed.
Lemma lem117572 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : True = (term154 P p m).
Proof. exact (SYM (@lem117571 P p m h1 h2)). Qed.
Lemma lem117573 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term144 P m) (h2 : p = (S m)) : term154 P p m.
Proof. exact (EQ_MP (@lem117572 P p m h1 h2) (@lem0)). Qed.
Lemma lem117585 (p : nat) (m : nat) : term162 p m.
Proof. exact (@lem82 (p = (S m))). Qed.
Lemma lem117605 (p : nat) (m : nat) (h1 : term2 p m) : (p = (S m)) = False.
Proof. exact (@lem117585 p m (@lem116999 p m h1)). Qed.
Lemma lem117606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem117607 (p : nat) (m : nat) (h1 : term2 p m) : (term157 p m) = (or False).
Proof. exact (MK_COMB (@lem117606) (@lem117605 p m h1)). Qed.
Lemma lem117608 (p : nat) (m : nat) : (Peano.le p m) = (Peano.le p m).
Proof. exact (eq_refl (Peano.le p m)). Qed.
Lemma lem117609 (p : nat) (m : nat) (h1 : term2 p m) : (term8 p m) = (term163 p m).
Proof. exact (MK_COMB (@lem117607 p m h1) (@lem117608 p m)). Qed.
Lemma lem117611 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem117612 (p : nat) (m : nat) : (term163 p m) = (Peano.le p m).
Proof. exact (@lem117611 (Peano.le p m)). Qed.
Lemma lem117613 (p : nat) (m : nat) (h1 : term2 p m) : (term8 p m) = (Peano.le p m).
Proof. exact (TRANS (@lem117609 p m h1) (@lem117612 p m)). Qed.
Lemma lem117614 (P : nat -> Prop) (p : nat) : (term97 P p) = (term97 P p).
Proof. exact (eq_refl (term97 P p)). Qed.
Lemma lem117615 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term2 p m) : (term149 P p m) = (term152 P p m).
Proof. exact (MK_COMB (@lem117614 P p) (@lem117613 p m h1)). Qed.
Lemma lem117618 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem117619 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term2 p m) : (term151 P p m) = (term164 P p m).
Proof. exact (MK_COMB (@lem117618) (@lem117615 P p m h1)). Qed.
Lemma lem117622 (P : nat -> Prop) (p : nat) (m : nat) : (term152 P p m) = (term152 P p m).
Proof. exact (eq_refl (term152 P p m)). Qed.
Lemma lem117623 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term2 p m) : (term154 P p m) = (term165 P p m).
Proof. exact (MK_COMB (@lem117619 P p m h1) (@lem117622 P p m)). Qed.
Lemma lem117625 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem117626 (P : nat -> Prop) (p : nat) (m : nat) : (term165 P p m) = True.
Proof. exact (@lem117625 (term152 P p m)). Qed.
Lemma lem117627 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term2 p m) : (term154 P p m) = True.
Proof. exact (TRANS (@lem117623 P p m h1) (@lem117626 P p m)). Qed.
Lemma lem117628 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term2 p m) : True = (term154 P p m).
Proof. exact (SYM (@lem117627 P p m h1)). Qed.
Lemma lem117629 (P : nat -> Prop) (p : nat) (m : nat) (h1 : term2 p m) : term154 P p m.
Proof. exact (EQ_MP (@lem117628 P p m h1) (@lem0)). Qed.
Lemma lem117630 (p : nat) (P : nat -> Prop) (m : nat) (h1 : term144 P m) : term154 P p m.
Proof. exact (or_elim (@lem116997 p m) (fun h0 : p = (S m) => @lem117573 P p m h1 h0) (fun h0 : term2 p m => @lem117629 P p m h0)). Qed.
Lemma lem117631 (p : nat) (P : nat -> Prop) (m : nat) (h1 : term144 P m) : term153 P p m.
Proof. exact (EQ_MP (@lem117485 P p m) (@lem117630 p P m h1)). Qed.
Lemma lem117632 (p : nat) (P : nat -> Prop) (m : nat) (h1 : term131 P m) (h2 : term144 P m) : term152 P p m.
Proof. exact (@lem117631 p P m h2 (@lem117461 p P m h1)). Qed.
Lemma lem117637 (P : nat -> Prop) (m : nat) (h1 : term131 P m) (h2 : term144 P m) : term49 P m.
Proof. exact (fun p : nat => @lem117632 p P m h1 h2). Qed.
Lemma lem117638 (P : nat -> Prop) (m : nat) (h1 : term131 P m) (h2 : term144 P m) : term146 P m.
Proof. exact (EQ_MP (@lem117458 P m) (@lem117637 P m h1 h2)). Qed.
Lemma lem117639 (P : nat -> Prop) (m : nat) (h1 : term131 P m) : term143 P m.
Proof. exact (fun h0 : term144 P m => @lem117638 P m h1 h0). Qed.
Lemma lem117640 (P : nat -> Prop) (m : nat) (h1 : term131 P m) : term142 P m.
Proof. exact (EQ_MP (@lem117447 P m) (@lem117639 P m h1)). Qed.
Lemma lem117641 (P : nat -> Prop) (m : nat) (h1 : term131 P m) : term141 P m.
Proof. exact (EQ_MP (@lem117445 P m) (@lem117640 P m h1)). Qed.
Lemma lem117642 (m : nat) (P : nat -> Prop) (h1 : term127 m P) : term128 m P.
Proof. exact (proj2 (@lem117391 m P h1)). Qed.
Lemma lem117643 (m : nat) (P : nat -> Prop) (h1 : term127 m P) : term131 P m.
Proof. exact (proj1 (@lem117391 m P h1)). Qed.
Lemma lem117644 (m : nat) (P : nat -> Prop) (h1 : term131 P m) (h2 : term128 m P) : term140 P m.
Proof. exact (@lem117641 P m h1 (@lem117395 m P h2)). Qed.
Lemma lem117645 (m : nat) (P : nat -> Prop) (h1 : term131 P m) (h2 : term128 m P) : (term131 P m) = (term140 P m).
Proof. exact (prop_ext (fun h3 : term131 P m => @lem117644 m P h1 h2) (fun h3 : term140 P m => @lem117396 P m h1)). Qed.
Lemma lem117646 (m : nat) (P : nat -> Prop) (h1 : term131 P m) (h2 : term128 m P) : term140 P m.
Proof. exact (EQ_MP (@lem117645 m P h1 h2) (@lem117396 P m h1)). Qed.
Lemma lem117647 (m : nat) (P : nat -> Prop) (h1 : term131 P m) (h2 : term127 m P) : (term128 m P) = (term140 P m).
Proof. exact (prop_ext (fun h3 : term128 m P => @lem117646 m P h1 h3) (fun h3 : term140 P m => @lem117642 m P h2)). Qed.
Lemma lem117648 (m : nat) (P : nat -> Prop) (h1 : term131 P m) (h2 : term127 m P) : term140 P m.
Proof. exact (EQ_MP (@lem117647 m P h1 h2) (@lem117642 m P h2)). Qed.
Lemma lem117649 (m : nat) (P : nat -> Prop) (h1 : term127 m P) : (term131 P m) = (term140 P m).
Proof. exact (prop_ext (fun h2 : term131 P m => @lem117648 m P h2 h1) (fun h2 : term140 P m => @lem117643 m P h1)). Qed.
Lemma lem117650 (m : nat) (P : nat -> Prop) (h1 : term127 m P) : term140 P m.
Proof. exact (EQ_MP (@lem117649 m P h1) (@lem117643 m P h1)). Qed.
Lemma lem117651 (P : nat -> Prop) (m : nat) : term82 P m.
Proof. exact (fun h0 : term127 m P => @lem117650 m P h0). Qed.
Lemma lem117652 (P : nat -> Prop) (m : nat) : term84 P m.
Proof. exact (fun h0 : term70 P m => @lem117651 P m). Qed.
Lemma lem117657 (P : nat -> Prop) : term88 P.
Proof. exact (fun m : nat => @lem117652 P m). Qed.
Lemma lem117658 (P : nat -> Prop) (a : nat) (h1 : P a) : term90 P.
Proof. exact (conj (@lem117390 P a h1) (@lem117657 P)). Qed.
Lemma lem117659 (P : nat -> Prop) (a : nat) (h1 : P a) : term95 P.
Proof. exact (@lem117272 P (@lem117658 P a h1)). Qed.
Lemma lem117660 (m : nat) (P : nat -> Prop) (a : nat) (h1 : P a) : term78 P m.
Proof. exact (@lem117659 P a h1 m). Qed.
Lemma lem117661 (P : nat -> Prop) (m : nat) : (term78 P m) = (term70 P m).
Proof. exact (eq_refl (term78 P m)). Qed.
Lemma lem117662 (m : nat) (P : nat -> Prop) (a : nat) (h1 : P a) : term70 P m.
Proof. exact (EQ_MP (@lem117661 P m) (@lem117660 m P a h1)). Qed.
Lemma lem117663 (m : nat) (P : nat -> Prop) (a : nat) (h1 : P a) : term69 P m.
Proof. exact (EQ_MP (@lem117249 P m) (@lem117662 m P a h1)). Qed.
Lemma lem117664 (a : nat) (m : nat) (P : nat -> Prop) (h1 : P a) (h2 : term65 m P) : term166 P m.
Proof. exact (@lem117663 m P a h1 (@lem117223 m P h2)). Qed.
Lemma lem117665 (a : nat) (m : nat) (P : nat -> Prop) (h1 : P a) (h2 : term65 m P) : term167 P.
Proof. exact (ex_intro (term168 P) m (@lem117664 a m P h1 h2)). Qed.
Lemma lem117666 (m : nat) (P : nat -> Prop) (a : nat) (h1 : P a) : term169 m P.
Proof. exact (fun h0 : term65 m P => @lem117665 a m P h1 h0). Qed.
Lemma lem117667 (a : nat) (m : nat) (P : nat -> Prop) (h1 : P a) (h2 : term65 m P) : term167 P.
Proof. exact (@lem117666 m P a h1 (@lem117222 m P h2)). Qed.
Lemma lem117668 (P : nat -> Prop) (a : nat) (h1 : term44 P) (h2 : P a) : term167 P.
Proof. exact (ex_elim (@lem117221 P h1) (fun m : nat => fun h0 : term67 P m => @lem117667 a m P h2 h0)). Qed.
Lemma lem117669 (P : nat -> Prop) (a : nat) (h1 : P a) : term170 P.
Proof. exact (fun h0 : term44 P => @lem117668 P a h0 h1). Qed.
Lemma lem117670 (P : nat -> Prop) (h1 : term43 P) : term44 P.
Proof. exact (proj2 (@lem117186 P h1)). Qed.
Lemma lem117671 (P : nat -> Prop) (h1 : term43 P) : term41 P.
Proof. exact (proj1 (@lem117186 P h1)). Qed.
Lemma lem117672 (P : nat -> Prop) (a : nat) (h1 : term44 P) (h2 : P a) : term167 P.
Proof. exact (@lem117669 P a h2 (@lem117187 P h1)). Qed.
Lemma lem117673 (P : nat -> Prop) (h1 : term44 P) (h2 : term41 P) : term167 P.
Proof. exact (ex_elim (@lem117188 P h2) (fun a : nat => fun h0 : term122 P a => @lem117672 P a h1 h0)). Qed.
Lemma lem117674 (P : nat -> Prop) (h1 : term41 P) (h2 : term43 P) : (term44 P) = (term167 P).
Proof. exact (prop_ext (fun h3 : term44 P => @lem117673 P h3 h1) (fun h3 : term167 P => @lem117670 P h2)). Qed.
Lemma lem117675 (P : nat -> Prop) (h1 : term41 P) (h2 : term43 P) : term167 P.
Proof. exact (EQ_MP (@lem117674 P h1 h2) (@lem117670 P h2)). Qed.
Lemma lem117676 (P : nat -> Prop) (h1 : term43 P) : (term41 P) = (term167 P).
Proof. exact (prop_ext (fun h2 : term41 P => @lem117675 P h2 h1) (fun h2 : term167 P => @lem117671 P h1)). Qed.
Lemma lem117677 (P : nat -> Prop) (h1 : term43 P) : term167 P.
Proof. exact (EQ_MP (@lem117676 P h1) (@lem117671 P h1)). Qed.
Lemma lem117678 (P : nat -> Prop) : term171 P.
Proof. exact (fun h0 : term43 P => @lem117677 P h0). Qed.
Lemma lem117679 (P : nat -> Prop) (h1 : term167 P) : term167 P.
Proof. exact (h1). Qed.
Lemma lem117680 (P : nat -> Prop) (m : nat) (h1 : term166 P m) : term166 P m.
Proof. exact (h1). Qed.
Lemma lem117681 (P : nat -> Prop) (m : nat) (h1 : term49 P m) : term49 P m.
Proof. exact (h1). Qed.
Lemma lem117682 (P : nat -> Prop) (m : nat) (h1 : P m) : P m.
Proof. exact (h1). Qed.
Lemma lem117683 (P : nat -> Prop) (m : nat) : (P m) = ((P m) = True).
Proof. exact (@lem7 (P m)). Qed.
Lemma lem117691 (P : nat -> Prop) (m : nat) (h1 : P m) : (P m) = True.
Proof. exact (EQ_MP (@lem117683 P m) (@lem117682 P m h1)). Qed.
Lemma lem117692 (P : nat -> Prop) (m : nat) (h1 : P m) : True = (P m).
Proof. exact (SYM (@lem117691 P m h1)). Qed.
Lemma lem117693 (P : nat -> Prop) (m : nat) (h1 : P m) : P m.
Proof. exact (EQ_MP (@lem117692 P m h1) (@lem0)). Qed.
Lemma lem117696 (x : nat) (P : nat -> Prop) (m : nat) (h1 : term49 P m) : term172 P m x.
Proof. exact (@lem117681 P m h1 x). Qed.
Lemma lem117697 (P : nat -> Prop) (x : nat) (m : nat) : (term172 P m x) = (term152 P x m).
Proof. exact (eq_refl (term172 P m x)). Qed.
Lemma lem117698 (x : nat) (P : nat -> Prop) (m : nat) (h1 : term49 P m) : term152 P x m.
Proof. exact (EQ_MP (@lem117697 P x m) (@lem117696 x P m h1)). Qed.
Lemma lem117699 (P : nat -> Prop) (x : nat) (m : nat) : (term152 P x m) = ((term152 P x m) = True).
Proof. exact (@lem7 (term152 P x m)). Qed.
Lemma lem117706 (x : nat) (P : nat -> Prop) (m : nat) (h1 : term49 P m) : (term152 P x m) = True.
Proof. exact (EQ_MP (@lem117699 P x m) (@lem117698 x P m h1)). Qed.
Lemma lem117707 (P : nat -> Prop) (m : nat) (h1 : term49 P m) : (term173 P m) = term110.
Proof. exact (fun_ext (fun x : nat => @lem117706 x P m h1)). Qed.
Lemma lem117708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem117709 (P : nat -> Prop) (m : nat) (h1 : term49 P m) : (term49 P m) = term112.
Proof. exact (MK_COMB (@lem117708) (@lem117707 P m h1)). Qed.
Lemma lem117711 {A : Type'} (t : Prop) : (term113 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem117712 (t : Prop) : (term114 t) = t.
Proof. exact (@lem117711 nat t). Qed.
Lemma lem117713 : term112 = True.
Proof. exact (@lem117712 True). Qed.
Lemma lem117714 (P : nat -> Prop) (m : nat) (h1 : term49 P m) : (term49 P m) = True.
Proof. exact (TRANS (@lem117709 P m h1) (@lem117713)). Qed.
Lemma lem117715 (P : nat -> Prop) (m : nat) (h1 : term49 P m) : True = (term49 P m).
Proof. exact (SYM (@lem117714 P m h1)). Qed.
Lemma lem117716 (P : nat -> Prop) (m : nat) (h1 : term49 P m) : term49 P m.
Proof. exact (EQ_MP (@lem117715 P m h1) (@lem0)). Qed.
Lemma lem117717 (P : nat -> Prop) (m : nat) (h1 : term49 P m) : term44 P.
Proof. exact (ex_intro (term47 P) m (@lem117716 P m h1)). Qed.
Lemma lem117718 (P : nat -> Prop) (m : nat) (h1 : P m) : term41 P.
Proof. exact (ex_intro (term122 P) m (@lem117693 P m h1)). Qed.
Lemma lem117719 (P : nat -> Prop) (m : nat) (h1 : term49 P m) (h2 : P m) : term43 P.
Proof. exact (conj (@lem117718 P m h2) (@lem117717 P m h1)). Qed.
Lemma lem117720 (P : nat -> Prop) (m : nat) (h1 : term166 P m) : term49 P m.
Proof. exact (proj2 (@lem117680 P m h1)). Qed.
Lemma lem117721 (P : nat -> Prop) (m : nat) (h1 : term166 P m) : P m.
Proof. exact (proj1 (@lem117680 P m h1)). Qed.
Lemma lem117722 (P : nat -> Prop) (m : nat) (h1 : term49 P m) (h2 : P m) : (term49 P m) = (term43 P).
Proof. exact (prop_ext (fun h3 : term49 P m => @lem117719 P m h1 h2) (fun h3 : term43 P => @lem117681 P m h1)). Qed.
Lemma lem117723 (P : nat -> Prop) (m : nat) (h1 : term49 P m) (h2 : P m) : term43 P.
Proof. exact (EQ_MP (@lem117722 P m h1 h2) (@lem117681 P m h1)). Qed.
Lemma lem117724 (P : nat -> Prop) (m : nat) (h1 : term49 P m) (h2 : P m) : (P m) = (term43 P).
Proof. exact (prop_ext (fun h3 : P m => @lem117723 P m h1 h2) (fun h3 : term43 P => @lem117682 P m h2)). Qed.
Lemma lem117725 (P : nat -> Prop) (m : nat) (h1 : term49 P m) (h2 : P m) : term43 P.
Proof. exact (EQ_MP (@lem117724 P m h1 h2) (@lem117682 P m h2)). Qed.
Lemma lem117726 (P : nat -> Prop) (m : nat) (h1 : P m) (h2 : term166 P m) : (term49 P m) = (term43 P).
Proof. exact (prop_ext (fun h3 : term49 P m => @lem117725 P m h3 h1) (fun h3 : term43 P => @lem117720 P m h2)). Qed.
Lemma lem117727 (P : nat -> Prop) (m : nat) (h1 : P m) (h2 : term166 P m) : term43 P.
Proof. exact (EQ_MP (@lem117726 P m h1 h2) (@lem117720 P m h2)). Qed.
Lemma lem117728 (P : nat -> Prop) (m : nat) (h1 : term166 P m) : (P m) = (term43 P).
Proof. exact (prop_ext (fun h2 : P m => @lem117727 P m h2 h1) (fun h2 : term43 P => @lem117721 P m h1)). Qed.
Lemma lem117729 (P : nat -> Prop) (m : nat) (h1 : term166 P m) : term43 P.
Proof. exact (EQ_MP (@lem117728 P m h1) (@lem117721 P m h1)). Qed.
Lemma lem117730 (P : nat -> Prop) (h1 : term167 P) : term43 P.
Proof. exact (ex_elim (@lem117679 P h1) (fun m : nat => fun h0 : term168 P m => @lem117729 P m h0)). Qed.
Lemma lem117731 (P : nat -> Prop) : term174 P.
Proof. exact (fun h0 : term167 P => @lem117730 P h0). Qed.
Lemma lem117732 (P : nat -> Prop) : term175 P.
Proof. exact (conj (@lem117678 P) (@lem117731 P)). Qed.
Lemma lem117733 (P : nat -> Prop) : (term175 P) = ((term43 P) = (term167 P)).
Proof. exact (@lem32 (term43 P) (term167 P)). Qed.
Lemma lem117734 (P : nat -> Prop) : (term43 P) = (term167 P).
Proof. exact (EQ_MP (@lem117733 P) (@lem117732 P)). Qed.
Lemma lem117739 : term176.
Proof. exact (fun P : nat -> Prop => @lem117734 P). Qed.
