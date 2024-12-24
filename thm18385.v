Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18385_term_abbrevs.
Require Import thm0_spec.
Require Import thm17934_spec.
Require Import thm17935_spec.
Require Import thm17943_spec.
Require Import thm17944_spec.
Require Import thm17949_spec.
Require Import thm17950_spec.
Require Import thm17957_spec.
Require Import thm17960_spec.
Require Import thm17961_spec.
Require Import thm17963_spec.
Require Import thm17964_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem18069 {A : Type'} : (@ex1 A) = (term0 A).
Proof. exact (@ex1_def A). Qed.
Lemma lem18086 {A : Type'} (P : A -> Prop) : (term1 A P) = (term1 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem18087 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (MK_COMB (@lem18069 A) (@lem18086 A P)). Qed.
Lemma lem18089 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem18090 {A : Type'} (f : type686 A) (y : A -> Prop) : (term5 A f y) = (f y).
Proof. exact (@lem18089 (A -> Prop) Prop f y). Qed.
Lemma lem18091 {A : Type'} (P : A -> Prop) : (term6 A P) = (term3 A P).
Proof. exact (@lem18090 A (term0 A) (term1 A P)). Qed.
Lemma lem18092 {A : Type'} (P : A -> Prop) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem18093 {A : Type'} : (term9 A) = (term0 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem18092 A P)). Qed.
Lemma lem18094 {A : Type'} (P : A -> Prop) : (term1 A P) = (term1 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem18095 {A : Type'} (P : A -> Prop) : (term6 A P) = (term3 A P).
Proof. exact (MK_COMB (@lem18093 A) (@lem18094 A P)). Qed.
Lemma lem18096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18097 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (MK_COMB (@lem18096) (@lem18095 A P)). Qed.
Lemma lem18098 {A : Type'} (P : A -> Prop) : (term3 A P) = (term12 A P).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem18099 {A : Type'} (P : A -> Prop) : ((term6 A P) = (term3 A P)) = ((term3 A P) = (term12 A P)).
Proof. exact (MK_COMB (@lem18097 A P) (@lem18098 A P)). Qed.
Lemma lem18100 {A : Type'} (P : A -> Prop) : (term3 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem18099 A P) (@lem18091 A P)). Qed.
Lemma lem18120 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem18121 {A : Type'} (f : A -> Prop) (y : A) : (term13 A f y) = (f y).
Proof. exact (@lem18120 A Prop f y). Qed.
Lemma lem18122 {A : Type'} (P : A -> Prop) (x : A) : (term13 A P x) = (P x).
Proof. exact (@lem18121 A P x). Qed.
Lemma lem18123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem18124 {A : Type'} (P : A -> Prop) (x : A) : (term14 A P x) = (term15 A P x).
Proof. exact (MK_COMB (@lem18123) (@lem18122 A P x)). Qed.
Lemma lem18126 {A B : Type'} (f : A -> B) (y : A) : (term4 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem18127 {A : Type'} (f : A -> Prop) (y : A) : (term13 A f y) = (f y).
Proof. exact (@lem18126 A Prop f y). Qed.
Lemma lem18128 {A : Type'} (P : A -> Prop) (y : A) : (term13 A P y) = (P y).
Proof. exact (@lem18127 A P y). Qed.
Lemma lem18129 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term16 A x P y) = (term17 A x P y).
Proof. exact (MK_COMB (@lem18124 A P x) (@lem18128 A P y)). Qed.
Lemma lem18132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem18133 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term18 A x P y) = (term19 A x P y).
Proof. exact (MK_COMB (@lem18132) (@lem18129 A x P y)). Qed.
Lemma lem18136 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem18137 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term20 A P x y) = (term21 A P x y).
Proof. exact (MK_COMB (@lem18133 A x P y) (@lem18136 A x y)). Qed.
Lemma lem18140 {A : Type'} (P : A -> Prop) (x : A) : (term22 A P x) = (term23 A P x).
Proof. exact (fun_ext (fun y : A => @lem18137 A P x y)). Qed.
Lemma lem18141 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18142 {A : Type'} (P : A -> Prop) (x : A) : (term24 A P x) = (term25 A P x).
Proof. exact (MK_COMB (@lem18141 A) (@lem18140 A P x)). Qed.
Lemma lem18147 {A : Type'} (P : A -> Prop) : (term26 A P) = (term27 A P).
Proof. exact (fun_ext (fun x : A => @lem18142 A P x)). Qed.
Lemma lem18148 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18149 {A : Type'} (P : A -> Prop) : (term28 A P) = (term29 A P).
Proof. exact (MK_COMB (@lem18148 A) (@lem18147 A P)). Qed.
Lemma lem18154 {A : Type'} (P : A -> Prop) : (term30 A P) = (term30 A P).
Proof. exact (eq_refl (term30 A P)). Qed.
Lemma lem18155 {A : Type'} (P : A -> Prop) : (term12 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem18154 A P) (@lem18149 A P)). Qed.
Lemma lem18158 {A : Type'} (P : A -> Prop) : (term3 A P) = (term31 A P).
Proof. exact (TRANS (@lem18100 A P) (@lem18155 A P)). Qed.
Lemma lem18159 {A : Type'} (P : A -> Prop) : (term2 A P) = (term31 A P).
Proof. exact (TRANS (@lem18087 A P) (@lem18158 A P)). Qed.
Lemma lem18160 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem18161 {A : Type'} (P : A -> Prop) : (term32 A P) = (term33 A P).
Proof. exact (MK_COMB (@lem18160) (@lem18159 A P)). Qed.
Lemma lem18163 (t1 : Prop) (t2 : Prop) : (term34 t1 t2) = (term35 t1 t2).
Proof. exact (proj1 (@lem17957 t1 t2)). Qed.
Lemma lem18164 {A : Type'} (P : A -> Prop) : (term33 A P) = (term36 A P).
Proof. exact (@lem18163 (term37 A P) (term29 A P)). Qed.
Lemma lem18168 {A : Type'} (P : A -> Prop) : (term38 A P) = (term39 A P).
Proof. exact (EQ_MP (@lem17964 A P) (@lem17963 A P)). Qed.
Lemma lem18169 {A : Type'} (P : A -> Prop) : (term38 A P) = (term39 A P).
Proof. exact (@lem18168 A P). Qed.
Lemma lem18174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem18175 {A : Type'} (P : A -> Prop) : (term40 A P) = (term41 A P).
Proof. exact (MK_COMB (@lem18174) (@lem18169 A P)). Qed.
Lemma lem18177 {A : Type'} (P : A -> Prop) : (term42 A P) = (term43 A P).
Proof. exact (EQ_MP (@lem17961 A P) (@lem17960 A P)). Qed.
Lemma lem18178 {A : Type'} (P : A -> Prop) : (term42 A P) = (term43 A P).
Proof. exact (@lem18177 A P). Qed.
Lemma lem18179 {A : Type'} (P : A -> Prop) : (term44 A P) = (term45 A P).
Proof. exact (@lem18178 A (term27 A P)). Qed.
Lemma lem18180 {A : Type'} (P : A -> Prop) (x : A) : (term46 A P x) = (term25 A P x).
Proof. exact (eq_refl (term46 A P x)). Qed.
Lemma lem18181 {A : Type'} (P : A -> Prop) : (term47 A P) = (term27 A P).
Proof. exact (fun_ext (fun x : A => @lem18180 A P x)). Qed.
Lemma lem18182 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18183 {A : Type'} (P : A -> Prop) : (term48 A P) = (term29 A P).
Proof. exact (MK_COMB (@lem18182 A) (@lem18181 A P)). Qed.
Lemma lem18184 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem18185 {A : Type'} (P : A -> Prop) : (term44 A P) = (term49 A P).
Proof. exact (MK_COMB (@lem18184) (@lem18183 A P)). Qed.
Lemma lem18186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18187 {A : Type'} (P : A -> Prop) : (term50 A P) = (term51 A P).
Proof. exact (MK_COMB (@lem18186) (@lem18185 A P)). Qed.
Lemma lem18188 {A : Type'} (P : A -> Prop) (x : A) : (term46 A P x) = (term25 A P x).
Proof. exact (eq_refl (term46 A P x)). Qed.
Lemma lem18189 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem18190 {A : Type'} (P : A -> Prop) (x : A) : (term52 A P x) = (term53 A P x).
Proof. exact (MK_COMB (@lem18189) (@lem18188 A P x)). Qed.
Lemma lem18191 {A : Type'} (P : A -> Prop) : (term54 A P) = (term55 A P).
Proof. exact (fun_ext (fun x : A => @lem18190 A P x)). Qed.
Lemma lem18192 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem18193 {A : Type'} (P : A -> Prop) : (term45 A P) = (term56 A P).
Proof. exact (MK_COMB (@lem18192 A) (@lem18191 A P)). Qed.
Lemma lem18194 {A : Type'} (P : A -> Prop) : ((term44 A P) = (term45 A P)) = ((term49 A P) = (term56 A P)).
Proof. exact (MK_COMB (@lem18187 A P) (@lem18193 A P)). Qed.
Lemma lem18195 {A : Type'} (P : A -> Prop) : (term49 A P) = (term56 A P).
Proof. exact (EQ_MP (@lem18194 A P) (@lem18179 A P)). Qed.
Lemma lem18201 {A : Type'} (P : A -> Prop) : (term42 A P) = (term43 A P).
Proof. exact (EQ_MP (@lem17961 A P) (@lem17960 A P)). Qed.
Lemma lem18202 {A : Type'} (P : A -> Prop) : (term42 A P) = (term43 A P).
Proof. exact (@lem18201 A P). Qed.
Lemma lem18203 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term58 A P x).
Proof. exact (@lem18202 A (term23 A P x)). Qed.
Lemma lem18204 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term59 A P x y) = (term21 A P x y).
Proof. exact (eq_refl (term59 A P x y)). Qed.
Lemma lem18205 {A : Type'} (P : A -> Prop) (x : A) : (term60 A P x) = (term23 A P x).
Proof. exact (fun_ext (fun y : A => @lem18204 A P x y)). Qed.
Lemma lem18206 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18207 {A : Type'} (P : A -> Prop) (x : A) : (term61 A P x) = (term25 A P x).
Proof. exact (MK_COMB (@lem18206 A) (@lem18205 A P x)). Qed.
Lemma lem18208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem18209 {A : Type'} (P : A -> Prop) (x : A) : (term57 A P x) = (term53 A P x).
Proof. exact (MK_COMB (@lem18208) (@lem18207 A P x)). Qed.
Lemma lem18210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18211 {A : Type'} (P : A -> Prop) (x : A) : (term62 A P x) = (term63 A P x).
Proof. exact (MK_COMB (@lem18210) (@lem18209 A P x)). Qed.
Lemma lem18212 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term59 A P x y) = (term21 A P x y).
Proof. exact (eq_refl (term59 A P x y)). Qed.
Lemma lem18213 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem18214 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term64 A P x y) = (term65 A P x y).
Proof. exact (MK_COMB (@lem18213) (@lem18212 A P x y)). Qed.
Lemma lem18215 {A : Type'} (P : A -> Prop) (x : A) : (term66 A P x) = (term67 A P x).
Proof. exact (fun_ext (fun y : A => @lem18214 A P x y)). Qed.
Lemma lem18216 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem18217 {A : Type'} (P : A -> Prop) (x : A) : (term58 A P x) = (term68 A P x).
Proof. exact (MK_COMB (@lem18216 A) (@lem18215 A P x)). Qed.
Lemma lem18218 {A : Type'} (P : A -> Prop) (x : A) : ((term57 A P x) = (term58 A P x)) = ((term53 A P x) = (term68 A P x)).
Proof. exact (MK_COMB (@lem18211 A P x) (@lem18217 A P x)). Qed.
Lemma lem18219 {A : Type'} (P : A -> Prop) (x : A) : (term53 A P x) = (term68 A P x).
Proof. exact (EQ_MP (@lem18218 A P x) (@lem18203 A P x)). Qed.
Lemma lem18225 (t1 : Prop) (t2 : Prop) : (term69 t1 t2) = (term70 t1 t2).
Proof. exact (EQ_MP (@lem17950 t1 t2) (@lem17949 t1 t2)). Qed.
Lemma lem18226 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term65 A P x y) = (term71 A P x y).
Proof. exact (@lem18225 (term17 A x P y) (x = y)). Qed.
Lemma lem18233 {A : Type'} (P : A -> Prop) (x : A) : (term67 A P x) = (term72 A P x).
Proof. exact (fun_ext (fun y : A => @lem18226 A P x y)). Qed.
Lemma lem18234 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem18235 {A : Type'} (P : A -> Prop) (x : A) : (term68 A P x) = (term73 A P x).
Proof. exact (MK_COMB (@lem18234 A) (@lem18233 A P x)). Qed.
Lemma lem18240 {A : Type'} (P : A -> Prop) (x : A) : (term53 A P x) = (term73 A P x).
Proof. exact (TRANS (@lem18219 A P x) (@lem18235 A P x)). Qed.
Lemma lem18241 {A : Type'} (P : A -> Prop) : (term55 A P) = (term74 A P).
Proof. exact (fun_ext (fun x : A => @lem18240 A P x)). Qed.
Lemma lem18242 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem18243 {A : Type'} (P : A -> Prop) : (term56 A P) = (term75 A P).
Proof. exact (MK_COMB (@lem18242 A) (@lem18241 A P)). Qed.
Lemma lem18248 {A : Type'} (P : A -> Prop) : (term49 A P) = (term75 A P).
Proof. exact (TRANS (@lem18195 A P) (@lem18243 A P)). Qed.
Lemma lem18249 {A : Type'} (P : A -> Prop) : (term36 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem18175 A P) (@lem18248 A P)). Qed.
Lemma lem18252 {A : Type'} (P : A -> Prop) : (term33 A P) = (term76 A P).
Proof. exact (TRANS (@lem18164 A P) (@lem18249 A P)). Qed.
Lemma lem18253 {A : Type'} (P : A -> Prop) : (term32 A P) = (term76 A P).
Proof. exact (TRANS (@lem18161 A P) (@lem18252 A P)). Qed.
Lemma lem18254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18255 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (MK_COMB (@lem18254) (@lem18253 A P)). Qed.
Lemma lem18276 {A : Type'} (P : A -> Prop) : (term79 A P) = (term79 A P).
Proof. exact (eq_refl (term79 A P)). Qed.
Lemma lem18277 {A : Type'} (P : A -> Prop) : ((term32 A P) = (term79 A P)) = ((term76 A P) = (term79 A P)).
Proof. exact (MK_COMB (@lem18255 A P) (@lem18276 A P)). Qed.
Lemma lem18280 {A : Type'} (P : A -> Prop) : ((term76 A P) = (term79 A P)) = ((term32 A P) = (term79 A P)).
Proof. exact (SYM (@lem18277 A P)). Qed.
Lemma lem18284 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem17935 A y x) (@lem17934 A x y)). Qed.
Lemma lem18285 (y : Prop) (x : Prop) : (x = y) = (y = x).
Proof. exact (@lem18284 Prop y x). Qed.
Lemma lem18286 {A : Type'} (P : A -> Prop) : ((term76 A P) = (term79 A P)) = ((term79 A P) = (term76 A P)).
Proof. exact (@lem18285 (term79 A P) (term76 A P)). Qed.
Lemma lem18308 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term80 t1 t2 t3) = (term81 t1 t2 t3).
Proof. exact (EQ_MP (@lem17944 t1 t2 t3) (@lem17943 t1 t2 t3)). Qed.
Lemma lem18309 {A : Type'} (P : A -> Prop) (y : A) (x : A) : (term82 A P y x) = (term83 A P y x).
Proof. exact (@lem18308 (P x) (P y) (term84 A y x)). Qed.
Lemma lem18317 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem17935 A y x) (@lem17934 A x y)). Qed.
Lemma lem18318 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (@lem18317 A y x). Qed.
Lemma lem18319 {A : Type'} (x : A) (y : A) : (y = x) = (x = y).
Proof. exact (@lem18318 A x y). Qed.
Lemma lem18325 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem18326 {A : Type'} (x : A) (y : A) : (term84 A y x) = (term84 A x y).
Proof. exact (MK_COMB (@lem18325) (@lem18319 A x y)). Qed.
Lemma lem18327 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term85 A x P y) = (term85 A x P y).
Proof. exact (eq_refl (term85 A x P y)). Qed.
Lemma lem18328 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term83 A P y x) = (term71 A P x y).
Proof. exact (MK_COMB (@lem18327 A x P y) (@lem18326 A x y)). Qed.
Lemma lem18331 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term82 A P y x) = (term71 A P x y).
Proof. exact (TRANS (@lem18309 A P y x) (@lem18328 A P x y)). Qed.
Lemma lem18332 {A : Type'} (P : A -> Prop) (x : A) : (term86 A P x) = (term72 A P x).
Proof. exact (fun_ext (fun y : A => @lem18331 A P x y)). Qed.
Lemma lem18333 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem18334 {A : Type'} (P : A -> Prop) (x : A) : (term87 A P x) = (term73 A P x).
Proof. exact (MK_COMB (@lem18333 A) (@lem18332 A P x)). Qed.
Lemma lem18339 {A : Type'} (P : A -> Prop) : (term88 A P) = (term74 A P).
Proof. exact (fun_ext (fun x : A => @lem18334 A P x)). Qed.
Lemma lem18340 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem18341 {A : Type'} (P : A -> Prop) : (term89 A P) = (term75 A P).
Proof. exact (MK_COMB (@lem18340 A) (@lem18339 A P)). Qed.
Lemma lem18346 {A : Type'} (P : A -> Prop) : (term41 A P) = (term41 A P).
Proof. exact (eq_refl (term41 A P)). Qed.
Lemma lem18347 {A : Type'} (P : A -> Prop) : (term79 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem18346 A P) (@lem18341 A P)). Qed.
Lemma lem18350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18351 {A : Type'} (P : A -> Prop) : (term90 A P) = (term78 A P).
Proof. exact (MK_COMB (@lem18350) (@lem18347 A P)). Qed.
Lemma lem18375 {A : Type'} (P : A -> Prop) : (term76 A P) = (term76 A P).
Proof. exact (eq_refl (term76 A P)). Qed.
Lemma lem18376 {A : Type'} (P : A -> Prop) : ((term79 A P) = (term76 A P)) = ((term76 A P) = (term76 A P)).
Proof. exact (MK_COMB (@lem18351 A P) (@lem18375 A P)). Qed.
Lemma lem18378 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem18379 (x : Prop) : (x = x) = True.
Proof. exact (@lem18378 Prop x). Qed.
Lemma lem18380 {A : Type'} (P : A -> Prop) : ((term76 A P) = (term76 A P)) = True.
Proof. exact (@lem18379 (term76 A P)). Qed.
Lemma lem18381 {A : Type'} (P : A -> Prop) : ((term79 A P) = (term76 A P)) = True.
Proof. exact (TRANS (@lem18376 A P) (@lem18380 A P)). Qed.
Lemma lem18382 {A : Type'} (P : A -> Prop) : ((term76 A P) = (term79 A P)) = True.
Proof. exact (TRANS (@lem18286 A P) (@lem18381 A P)). Qed.
Lemma lem18383 {A : Type'} (P : A -> Prop) : True = ((term76 A P) = (term79 A P)).
Proof. exact (SYM (@lem18382 A P)). Qed.
Lemma lem18384 {A : Type'} (P : A -> Prop) : (term76 A P) = (term79 A P).
Proof. exact (EQ_MP (@lem18383 A P) (@lem0)). Qed.
Lemma lem18385 {A : Type'} (P : A -> Prop) : (term32 A P) = (term79 A P).
Proof. exact (EQ_MP (@lem18280 A P) (@lem18384 A P)). Qed.
