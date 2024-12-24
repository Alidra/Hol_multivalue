Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BOUNDS_LINEAR_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import LE_ADD_spec.
Require Import LE_ADDR_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import LE_EXISTS_spec.
Require Import LT_EXISTS_spec.
Require Import LT_SUC_LE_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_LE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm10568_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1260090 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem1260091 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem1260090 m n p h1)). Qed.
Lemma lem1260092 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem1260093 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem1260092 m n p h1)). Qed.
Lemma lem1260094 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem1260091 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem1260093 m n p h1)). Qed.
Lemma lem1260095 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem1260094 m n p)). Qed.
Lemma lem1260096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1260097 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem1260096) (@lem1260095 m n)). Qed.
Lemma lem1260098 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1260097 m n)). Qed.
Lemma lem1260099 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1260100 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1260099) (@lem1260098 m)). Qed.
Lemma lem1260101 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1260100 m)). Qed.
Lemma lem1260102 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1260103 : term12 = term13.
Proof. exact (MK_COMB (@lem1260102) (@lem1260101)). Qed.
Lemma lem1260104 : term13.
Proof. exact (EQ_MP (@lem1260103) (@lem77960)). Qed.
Lemma lem1260105 (m : nat) : term14 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1260106 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1260107 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1260106 m) (@lem1260105 m)). Qed.
Lemma lem1260108 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1260107 m n). Qed.
Lemma lem1260109 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1260110 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1260109 m n) (@lem1260108 m n)). Qed.
Lemma lem1260111 (m : nat) (n : nat) : (term17 m n) = ((term17 m n) = True).
Proof. exact (@lem7 (term17 m n)). Qed.
Lemma lem1260113 (m : nat) : term18 m.
Proof. exact (@lem1260104 m). Qed.
Lemma lem1260114 (m : nat) : (term18 m) = (term9 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1260115 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1260114 m) (@lem1260113 m)). Qed.
Lemma lem1260116 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1260115 m n). Qed.
Lemma lem1260117 (m : nat) (n : nat) : (term19 m n) = (term5 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1260118 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem1260117 m n) (@lem1260116 m n)). Qed.
Lemma lem1260119 (m : nat) (n : nat) (p : nat) : term20 m n p.
Proof. exact (@lem1260118 m n p). Qed.
Lemma lem1260120 (m : nat) (n : nat) (p : nat) : (term20 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term20 m n p)). Qed.
Lemma lem1260122 (m : nat) : term21 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1260123 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1260124 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1260123 m) (@lem1260122 m)). Qed.
Lemma lem1260125 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1260124 m n). Qed.
Lemma lem1260126 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1260127 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1260126 m n) (@lem1260125 m n)). Qed.
Lemma lem1260128 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem1260127 m n p). Qed.
Lemma lem1260129 (m : nat) (n : nat) (p : nat) : (term25 m n p) = ((term26 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term25 m n p)). Qed.
Lemma lem1260131 (m : nat) : term28 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1260132 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1260133 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1260132 m) (@lem1260131 m)). Qed.
Lemma lem1260134 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1260133 m n). Qed.
Lemma lem1260135 (n : nat) (m : nat) : (term30 m n) = ((Peano.le m n) = (term31 n m)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1260137 (m : nat) : term32 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1260138 (m : nat) : (term32 m) = (term33 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1260139 (m : nat) : term33 m.
Proof. exact (EQ_MP (@lem1260138 m) (@lem1260137 m)). Qed.
Lemma lem1260140 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem1260139 m n). Qed.
Lemma lem1260141 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem1260142 (m : nat) (n : nat) : term35 m n.
Proof. exact (EQ_MP (@lem1260141 m n) (@lem1260140 m n)). Qed.
Lemma lem1260143 (m : nat) (n : nat) : (term35 m n) = ((term35 m n) = True).
Proof. exact (@lem7 (term35 m n)). Qed.
Lemma lem1260154 (m : nat) : term36 m.
Proof. exact (@lem91305 m). Qed.
Lemma lem1260155 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1260156 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1260155 m) (@lem1260154 m)). Qed.
Lemma lem1260157 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1260156 m n). Qed.
Lemma lem1260158 (m : nat) (n : nat) : (term38 m n) = ((term39 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1260160 : term40.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1260161 : term41.
Proof. exact (proj2 (@lem1260160)). Qed.
Lemma lem1260162 : term42.
Proof. exact (proj2 (@lem1260161)). Qed.
Lemma lem1260163 (m : nat) : term43 m.
Proof. exact (@lem1260162 m). Qed.
Lemma lem1260164 (m : nat) : (term43 m) = (term44 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem1260165 (m : nat) : term44 m.
Proof. exact (EQ_MP (@lem1260164 m) (@lem1260163 m)). Qed.
Lemma lem1260166 (m : nat) (n : nat) : term45 m n.
Proof. exact (@lem1260165 m n). Qed.
Lemma lem1260167 (m : nat) (n : nat) : (term45 m n) = ((term46 m n) = (term47 m n)).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem1260184 : term48.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1260185 : term49.
Proof. exact (proj2 (@lem1260184)). Qed.
Lemma lem1260186 : term50.
Proof. exact (proj2 (@lem1260185)). Qed.
Lemma lem1260187 : term51.
Proof. exact (proj2 (@lem1260186)). Qed.
Lemma lem1260188 : term52.
Proof. exact (proj2 (@lem1260187)). Qed.
Lemma lem1260189 (m : nat) : term53 m.
Proof. exact (@lem1260188 m). Qed.
Lemma lem1260190 (m : nat) : (term53 m) = (term54 m).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem1260191 (m : nat) : term54 m.
Proof. exact (EQ_MP (@lem1260190 m) (@lem1260189 m)). Qed.
Lemma lem1260192 (m : nat) (n : nat) : term55 m n.
Proof. exact (@lem1260191 m n). Qed.
Lemma lem1260193 (m : nat) (n : nat) : (term55 m n) = ((term56 m n) = (term57 m n)).
Proof. exact (eq_refl (term55 m n)). Qed.
Lemma lem1260195 : term58.
Proof. exact (proj1 (@lem1260187)). Qed.
Lemma lem1260196 (m : nat) : term59 m.
Proof. exact (@lem1260195 m). Qed.
Lemma lem1260197 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem1260198 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem1260197 m) (@lem1260196 m)). Qed.
Lemma lem1260199 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem1260198 m n). Qed.
Lemma lem1260200 (m : nat) (n : nat) : (term61 m n) = ((term62 m n) = (term63 m n)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem1260218 (m : nat) : term64 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1260219 (m : nat) : (term64 m) = (term65 m).
Proof. exact (eq_refl (term64 m)). Qed.
Lemma lem1260220 (m : nat) : term65 m.
Proof. exact (EQ_MP (@lem1260219 m) (@lem1260218 m)). Qed.
Lemma lem1260221 (m : nat) (n : nat) : term66 m n.
Proof. exact (@lem1260220 m n). Qed.
Lemma lem1260222 (n : nat) (m : nat) : (term66 m n) = ((term67 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term66 m n)). Qed.
Lemma lem1260224 (m : nat) : term68 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem1260225 (m : nat) : (term68 m) = (term69 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem1260226 (m : nat) : term69 m.
Proof. exact (EQ_MP (@lem1260225 m) (@lem1260224 m)). Qed.
Lemma lem1260227 (m : nat) (n : nat) : term70 m n.
Proof. exact (@lem1260226 m n). Qed.
Lemma lem1260228 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (eq_refl (term70 m n)). Qed.
Lemma lem1260229 (m : nat) (n : nat) : term71 m n.
Proof. exact (EQ_MP (@lem1260228 m n) (@lem1260227 m n)). Qed.
Lemma lem1260230 (m : nat) (n : nat) (p : nat) : term72 m n p.
Proof. exact (@lem1260229 m n p). Qed.
Lemma lem1260231 (m : nat) (n : nat) (p : nat) : (term72 m n p) = ((term73 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term72 m n p)). Qed.
Lemma lem1260233 (m : nat) : term21 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1260234 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1260235 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1260234 m) (@lem1260233 m)). Qed.
Lemma lem1260236 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1260235 m n). Qed.
Lemma lem1260237 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1260238 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1260237 m n) (@lem1260236 m n)). Qed.
Lemma lem1260239 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem1260238 m n p). Qed.
Lemma lem1260240 (m : nat) (n : nat) (p : nat) : (term25 m n p) = ((term26 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term25 m n p)). Qed.
Lemma lem1260242 (m : nat) : term74 m.
Proof. exact (@lem100361 m). Qed.
Lemma lem1260243 (m : nat) : (term74 m) = (term75 m).
Proof. exact (eq_refl (term74 m)). Qed.
Lemma lem1260244 (m : nat) : term75 m.
Proof. exact (EQ_MP (@lem1260243 m) (@lem1260242 m)). Qed.
Lemma lem1260245 (m : nat) (n : nat) : term76 m n.
Proof. exact (@lem1260244 m n). Qed.
Lemma lem1260246 (n : nat) (m : nat) : (term76 m n) = ((Peano.lt m n) = (term77 n m)).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem1260248 (m : nat) : term64 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1260249 (m : nat) : (term64 m) = (term65 m).
Proof. exact (eq_refl (term64 m)). Qed.
Lemma lem1260250 (m : nat) : term65 m.
Proof. exact (EQ_MP (@lem1260249 m) (@lem1260248 m)). Qed.
Lemma lem1260251 (m : nat) (n : nat) : term66 m n.
Proof. exact (@lem1260250 m n). Qed.
Lemma lem1260252 (n : nat) (m : nat) : (term66 m n) = ((term67 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term66 m n)). Qed.
Lemma lem1260254 (A : nat) (B : nat) (C : nat) : (term78 C A B) = (term79 A B C).
Proof. exact (@lem10568 (Peano.le A B) (term80 A B C)). Qed.
Lemma lem1260255 (C : nat) (A : nat) (B : nat) : (term79 A B C) = (term78 C A B).
Proof. exact (SYM (@lem1260254 A B C)). Qed.
Lemma lem1260259 (n : nat) (m : nat) : (term67 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1260252 n m) (@lem1260251 m n)). Qed.
Lemma lem1260260 (B : nat) (A : nat) : (term67 A B) = (Peano.lt B A).
Proof. exact (@lem1260259 B A). Qed.
Lemma lem1260261 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1260262 (B : nat) (A : nat) : (term81 A B) = (term82 B A).
Proof. exact (MK_COMB (@lem1260261) (@lem1260260 B A)). Qed.
Lemma lem1260267 (A : nat) (B : nat) (C : nat) : (term83 A B C) = (term83 A B C).
Proof. exact (eq_refl (term83 A B C)). Qed.
Lemma lem1260268 (A : nat) (B : nat) (C : nat) : (term79 A B C) = (term84 A B C).
Proof. exact (MK_COMB (@lem1260262 B A) (@lem1260267 A B C)). Qed.
Lemma lem1260271 (A : nat) (B : nat) (C : nat) : (term84 A B C) = (term79 A B C).
Proof. exact (SYM (@lem1260268 A B C)). Qed.
Lemma lem1260272 (B : nat) (A : nat) (h1 : Peano.lt B A) : Peano.lt B A.
Proof. exact (h1). Qed.
Lemma lem1260274 (n : nat) (m : nat) : (Peano.lt m n) = (term77 n m).
Proof. exact (EQ_MP (@lem1260246 n m) (@lem1260245 m n)). Qed.
Lemma lem1260275 (A : nat) (B : nat) : (Peano.lt B A) = (term77 A B).
Proof. exact (@lem1260274 A B). Qed.
Lemma lem1260282 (B : nat) (A : nat) (h1 : Peano.lt B A) : term77 A B.
Proof. exact (EQ_MP (@lem1260275 A B) (@lem1260272 B A h1)). Qed.
Lemma lem1260283 (A : nat) (B : nat) (d : nat) (h1 : A = (term46 B d)) : A = (term46 B d).
Proof. exact (h1). Qed.
Lemma lem1260284 (B : nat) (C : nat) : (term85 B C) = (term85 B C).
Proof. exact (eq_refl (term85 B C)). Qed.
Lemma lem1260285 (C : nat) (A : nat) (B : nat) (d : nat) (h1 : A = (term46 B d)) : (term86 B C A) = (term87 C B d).
Proof. exact (MK_COMB (@lem1260284 B C) (@lem1260283 A B d h1)). Qed.
Lemma lem1260286 (d : nat) (B : nat) (C : nat) : (term87 C B d) = (term88 d B C).
Proof. exact (eq_refl (term87 C B d)). Qed.
Lemma lem1260287 (B : nat) (C : nat) (A : nat) : (term89 B C A) = (term89 B C A).
Proof. exact (eq_refl (term89 B C A)). Qed.
Lemma lem1260288 (A : nat) (d : nat) (B : nat) (C : nat) : ((term86 B C A) = (term87 C B d)) = ((term86 B C A) = (term88 d B C)).
Proof. exact (MK_COMB (@lem1260287 B C A) (@lem1260286 d B C)). Qed.
Lemma lem1260289 (A : nat) (B : nat) (C : nat) : (term86 B C A) = (term83 A B C).
Proof. exact (eq_refl (term86 B C A)). Qed.
Lemma lem1260290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1260291 (A : nat) (B : nat) (C : nat) : (term89 B C A) = (term90 A B C).
Proof. exact (MK_COMB (@lem1260290) (@lem1260289 A B C)). Qed.
Lemma lem1260292 (d : nat) (B : nat) (C : nat) : (term88 d B C) = (term88 d B C).
Proof. exact (eq_refl (term88 d B C)). Qed.
Lemma lem1260293 (A : nat) (d : nat) (B : nat) (C : nat) : ((term86 B C A) = (term88 d B C)) = ((term83 A B C) = (term88 d B C)).
Proof. exact (MK_COMB (@lem1260291 A B C) (@lem1260292 d B C)). Qed.
Lemma lem1260294 (A : nat) (d : nat) (B : nat) (C : nat) : ((term86 B C A) = (term87 C B d)) = ((term83 A B C) = (term88 d B C)).
Proof. exact (TRANS (@lem1260288 A d B C) (@lem1260293 A d B C)). Qed.
Lemma lem1260295 (C : nat) (A : nat) (B : nat) (d : nat) (h1 : A = (term46 B d)) : (term83 A B C) = (term88 d B C).
Proof. exact (EQ_MP (@lem1260294 A d B C) (@lem1260285 C A B d h1)). Qed.
Lemma lem1260296 (C : nat) (A : nat) (B : nat) (d : nat) (h1 : A = (term46 B d)) : (term88 d B C) = (term83 A B C).
Proof. exact (SYM (@lem1260295 C A B d h1)). Qed.
Lemma lem1260302 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1260240 m n p) (@lem1260239 m n p)). Qed.
Lemma lem1260303 (B : nat) (d : nat) (n : nat) : (term91 B d n) = (term92 B d n).
Proof. exact (@lem1260302 B (S d) n). Qed.
Lemma lem1260304 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1260305 (B : nat) (d : nat) (n : nat) : (term93 B d n) = (term94 B d n).
Proof. exact (MK_COMB (@lem1260304) (@lem1260303 B d n)). Qed.
Lemma lem1260306 (B : nat) (n : nat) (C : nat) : (term95 B n C) = (term95 B n C).
Proof. exact (eq_refl (term95 B n C)). Qed.
Lemma lem1260307 (d : nat) (B : nat) (n : nat) (C : nat) : (term96 d B n C) = (term97 d B n C).
Proof. exact (MK_COMB (@lem1260305 B d n) (@lem1260306 B n C)). Qed.
Lemma lem1260309 (m : nat) (n : nat) (p : nat) : (term73 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1260231 m n p) (@lem1260230 m n p)). Qed.
Lemma lem1260310 (B : nat) (d : nat) (n : nat) (C : nat) : (term97 d B n C) = (term98 d n C).
Proof. exact (@lem1260309 (Nat.mul B n) (term62 d n) C). Qed.
Lemma lem1260311 (B : nat) (d : nat) (n : nat) (C : nat) : (term96 d B n C) = (term98 d n C).
Proof. exact (TRANS (@lem1260307 d B n C) (@lem1260310 B d n C)). Qed.
Lemma lem1260312 (B : nat) (d : nat) (C : nat) : (term99 d B C) = (term100 d C).
Proof. exact (fun_ext (fun n : nat => @lem1260311 B d n C)). Qed.
Lemma lem1260313 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1260314 (B : nat) (d : nat) (C : nat) : (term101 d B C) = (term102 d C).
Proof. exact (MK_COMB (@lem1260313) (@lem1260312 B d C)). Qed.
Lemma lem1260319 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1260320 (B : nat) (d : nat) (C : nat) : (term88 d B C) = (term103 d C).
Proof. exact (MK_COMB (@lem1260319) (@lem1260314 B d C)). Qed.
Lemma lem1260321 (d : nat) (B : nat) (C : nat) : (term103 d C) = (term88 d B C).
Proof. exact (SYM (@lem1260320 B d C)). Qed.
Lemma lem1260322 (d : nat) (C : nat) (h1 : term102 d C) : term102 d C.
Proof. exact (h1). Qed.
Lemma lem1260323 (d : nat) (C : nat) (h1 : term102 d C) : term104 d C.
Proof. exact (@lem1260322 d C h1 (S C)). Qed.
Lemma lem1260324 (d : nat) (C : nat) : (term104 d C) = (term105 d C).
Proof. exact (eq_refl (term104 d C)). Qed.
Lemma lem1260325 (d : nat) (C : nat) (h1 : term102 d C) : term105 d C.
Proof. exact (EQ_MP (@lem1260324 d C) (@lem1260323 d C h1)). Qed.
Lemma lem1260327 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1260328 (d : nat) (C : nat) : (term106 d C) = (term107 d C).
Proof. exact (@lem1260327 (term105 d C)). Qed.
Lemma lem1260330 (n : nat) (m : nat) : (term67 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1260222 n m) (@lem1260221 m n)). Qed.
Lemma lem1260331 (d : nat) (C : nat) : (term107 d C) = (term108 d C).
Proof. exact (@lem1260330 C (term109 d C)). Qed.
Lemma lem1260332 (d : nat) (C : nat) : (term106 d C) = (term108 d C).
Proof. exact (TRANS (@lem1260328 d C) (@lem1260331 d C)). Qed.
Lemma lem1260334 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem1260200 m n) (@lem1260199 m n)). Qed.
Lemma lem1260335 (d : nat) (C : nat) : (term109 d C) = (term110 d C).
Proof. exact (@lem1260334 d (S C)). Qed.
Lemma lem1260337 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (EQ_MP (@lem1260167 m n) (@lem1260166 m n)). Qed.
Lemma lem1260338 (d : nat) (C : nat) : (term110 d C) = (term111 d C).
Proof. exact (@lem1260337 (term56 d C) C). Qed.
Lemma lem1260339 (d : nat) (C : nat) : (term109 d C) = (term111 d C).
Proof. exact (TRANS (@lem1260335 d C) (@lem1260338 d C)). Qed.
Lemma lem1260341 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (EQ_MP (@lem1260193 m n) (@lem1260192 m n)). Qed.
Lemma lem1260342 (d : nat) (C : nat) : (term56 d C) = (term57 d C).
Proof. exact (@lem1260341 d C). Qed.
Lemma lem1260343 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1260344 (d : nat) (C : nat) : (term112 d C) = (term113 d C).
Proof. exact (MK_COMB (@lem1260343) (@lem1260342 d C)). Qed.
Lemma lem1260345 (C : nat) : C = C.
Proof. exact (eq_refl C). Qed.
Lemma lem1260346 (d : nat) (C : nat) : (term114 d C) = (term115 d C).
Proof. exact (MK_COMB (@lem1260344 d C) (@lem1260345 C)). Qed.
Lemma lem1260347 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1260348 (d : nat) (C : nat) : (term111 d C) = (term116 d C).
Proof. exact (MK_COMB (@lem1260347) (@lem1260346 d C)). Qed.
Lemma lem1260349 (d : nat) (C : nat) : (term109 d C) = (term116 d C).
Proof. exact (TRANS (@lem1260339 d C) (@lem1260348 d C)). Qed.
Lemma lem1260350 (C : nat) : (Peano.lt C) = (Peano.lt C).
Proof. exact (eq_refl (Peano.lt C)). Qed.
Lemma lem1260351 (d : nat) (C : nat) : (term108 d C) = (term117 d C).
Proof. exact (MK_COMB (@lem1260350 C) (@lem1260349 d C)). Qed.
Lemma lem1260353 (m : nat) (n : nat) : (term39 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1260158 m n) (@lem1260157 m n)). Qed.
Lemma lem1260354 (d : nat) (C : nat) : (term117 d C) = (term118 d C).
Proof. exact (@lem1260353 C (term115 d C)). Qed.
Lemma lem1260355 (d : nat) (C : nat) : (term108 d C) = (term118 d C).
Proof. exact (TRANS (@lem1260351 d C) (@lem1260354 d C)). Qed.
Lemma lem1260356 (d : nat) (C : nat) : (term106 d C) = (term118 d C).
Proof. exact (TRANS (@lem1260332 d C) (@lem1260355 d C)). Qed.
Lemma lem1260357 (d : nat) (C : nat) : (term118 d C) = (term106 d C).
Proof. exact (SYM (@lem1260356 d C)). Qed.
Lemma lem1260359 (m : nat) (n : nat) : (term35 m n) = True.
Proof. exact (EQ_MP (@lem1260143 m n) (@lem1260142 m n)). Qed.
Lemma lem1260360 (d : nat) (C : nat) : (term118 d C) = True.
Proof. exact (@lem1260359 (term57 d C) C). Qed.
Lemma lem1260361 (d : nat) (C : nat) : True = (term118 d C).
Proof. exact (SYM (@lem1260360 d C)). Qed.
Lemma lem1260362 (d : nat) (C : nat) : term118 d C.
Proof. exact (EQ_MP (@lem1260361 d C) (@lem0)). Qed.
Lemma lem1260363 (d : nat) (C : nat) : term106 d C.
Proof. exact (EQ_MP (@lem1260357 d C) (@lem1260362 d C)). Qed.
Lemma lem1260364 (d : nat) (C : nat) (h1 : term102 d C) : False.
Proof. exact (@lem1260363 d C (@lem1260325 d C h1)). Qed.
Lemma lem1260365 (d : nat) (C : nat) : term119 d C.
Proof. exact (fun h0 : term102 d C => @lem1260364 d C h0). Qed.
Lemma lem1260366 (d : nat) (C : nat) : (term119 d C) = (term103 d C).
Proof. exact (@lem69 (term102 d C)). Qed.
Lemma lem1260367 (d : nat) (C : nat) : term103 d C.
Proof. exact (EQ_MP (@lem1260366 d C) (@lem1260365 d C)). Qed.
Lemma lem1260368 (d : nat) (B : nat) (C : nat) : term88 d B C.
Proof. exact (EQ_MP (@lem1260321 d B C) (@lem1260367 d C)). Qed.
Lemma lem1260369 (C : nat) (A : nat) (B : nat) (d : nat) (h1 : A = (term46 B d)) : term83 A B C.
Proof. exact (EQ_MP (@lem1260296 C A B d h1) (@lem1260368 d B C)). Qed.
Lemma lem1260370 (C : nat) (B : nat) (A : nat) (h1 : Peano.lt B A) : term83 A B C.
Proof. exact (ex_elim (@lem1260282 B A h1) (fun d : nat => fun h0 : term120 A B d => @lem1260369 C A B d h0)). Qed.
Lemma lem1260371 (A : nat) (B : nat) (C : nat) : term84 A B C.
Proof. exact (fun h0 : Peano.lt B A => @lem1260370 C B A h0). Qed.
Lemma lem1260372 (A : nat) (B : nat) (C : nat) : term79 A B C.
Proof. exact (EQ_MP (@lem1260271 A B C) (@lem1260371 A B C)). Qed.
Lemma lem1260373 (C : nat) (A : nat) (B : nat) : term78 C A B.
Proof. exact (EQ_MP (@lem1260255 C A B) (@lem1260372 A B C)). Qed.
Lemma lem1260374 (A : nat) (B : nat) (h1 : Peano.le A B) : Peano.le A B.
Proof. exact (h1). Qed.
Lemma lem1260376 (n : nat) (m : nat) : (Peano.le m n) = (term31 n m).
Proof. exact (EQ_MP (@lem1260135 n m) (@lem1260134 m n)). Qed.
Lemma lem1260377 (B : nat) (A : nat) : (Peano.le A B) = (term31 B A).
Proof. exact (@lem1260376 B A). Qed.
Lemma lem1260384 (A : nat) (B : nat) (h1 : Peano.le A B) : term31 B A.
Proof. exact (EQ_MP (@lem1260377 B A) (@lem1260374 A B h1)). Qed.
Lemma lem1260385 (B : nat) (A : nat) (d : nat) (h1 : B = (Nat.add A d)) : B = (Nat.add A d).
Proof. exact (h1). Qed.
Lemma lem1260386 (A : nat) (C : nat) : (term121 A C) = (term121 A C).
Proof. exact (eq_refl (term121 A C)). Qed.
Lemma lem1260387 (C : nat) (B : nat) (A : nat) (d : nat) (h1 : B = (Nat.add A d)) : (term122 A C B) = (term123 C A d).
Proof. exact (MK_COMB (@lem1260386 A C) (@lem1260385 B A d h1)). Qed.
Lemma lem1260388 (A : nat) (d : nat) (C : nat) : (term123 C A d) = (term124 A d C).
Proof. exact (eq_refl (term123 C A d)). Qed.
Lemma lem1260389 (A : nat) (C : nat) (B : nat) : (term125 A C B) = (term125 A C B).
Proof. exact (eq_refl (term125 A C B)). Qed.
Lemma lem1260390 (B : nat) (A : nat) (d : nat) (C : nat) : ((term122 A C B) = (term123 C A d)) = ((term122 A C B) = (term124 A d C)).
Proof. exact (MK_COMB (@lem1260389 A C B) (@lem1260388 A d C)). Qed.
Lemma lem1260391 (A : nat) (B : nat) (C : nat) : (term122 A C B) = (term80 A B C).
Proof. exact (eq_refl (term122 A C B)). Qed.
Lemma lem1260392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1260393 (A : nat) (B : nat) (C : nat) : (term125 A C B) = (term126 A B C).
Proof. exact (MK_COMB (@lem1260392) (@lem1260391 A B C)). Qed.
Lemma lem1260394 (A : nat) (d : nat) (C : nat) : (term124 A d C) = (term124 A d C).
Proof. exact (eq_refl (term124 A d C)). Qed.
Lemma lem1260395 (B : nat) (A : nat) (d : nat) (C : nat) : ((term122 A C B) = (term124 A d C)) = ((term80 A B C) = (term124 A d C)).
Proof. exact (MK_COMB (@lem1260393 A B C) (@lem1260394 A d C)). Qed.
Lemma lem1260396 (B : nat) (A : nat) (d : nat) (C : nat) : ((term122 A C B) = (term123 C A d)) = ((term80 A B C) = (term124 A d C)).
Proof. exact (TRANS (@lem1260390 B A d C) (@lem1260395 B A d C)). Qed.
Lemma lem1260397 (C : nat) (B : nat) (A : nat) (d : nat) (h1 : B = (Nat.add A d)) : (term80 A B C) = (term124 A d C).
Proof. exact (EQ_MP (@lem1260396 B A d C) (@lem1260387 C B A d h1)). Qed.
Lemma lem1260398 (C : nat) (B : nat) (A : nat) (d : nat) (h1 : B = (Nat.add A d)) : (term124 A d C) = (term80 A B C).
Proof. exact (SYM (@lem1260397 C B A d h1)). Qed.
Lemma lem1260406 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1260129 m n p) (@lem1260128 m n p)). Qed.
Lemma lem1260407 (A : nat) (d : nat) (n : nat) : (term26 A d n) = (term27 A d n).
Proof. exact (@lem1260406 A d n). Qed.
Lemma lem1260408 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1260409 (A : nat) (d : nat) (n : nat) : (term127 A d n) = (term128 A d n).
Proof. exact (MK_COMB (@lem1260408) (@lem1260407 A d n)). Qed.
Lemma lem1260410 (C : nat) : C = C.
Proof. exact (eq_refl C). Qed.
Lemma lem1260411 (A : nat) (d : nat) (n : nat) (C : nat) : (term129 A d n C) = (term130 A d n C).
Proof. exact (MK_COMB (@lem1260409 A d n) (@lem1260410 C)). Qed.
Lemma lem1260413 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1260120 m n p) (@lem1260119 m n p)). Qed.
Lemma lem1260414 (A : nat) (d : nat) (n : nat) (C : nat) : (term130 A d n C) = (term131 A d n C).
Proof. exact (@lem1260413 (Nat.mul A n) (Nat.mul d n) C). Qed.
Lemma lem1260415 (A : nat) (d : nat) (n : nat) (C : nat) : (term129 A d n C) = (term131 A d n C).
Proof. exact (TRANS (@lem1260411 A d n C) (@lem1260414 A d n C)). Qed.
Lemma lem1260416 (A : nat) (n : nat) : (term132 A n) = (term132 A n).
Proof. exact (eq_refl (term132 A n)). Qed.
Lemma lem1260417 (A : nat) (d : nat) (n : nat) (C : nat) : (term133 A d n C) = (term134 A d n C).
Proof. exact (MK_COMB (@lem1260416 A n) (@lem1260415 A d n C)). Qed.
Lemma lem1260419 (m : nat) (n : nat) : (term17 m n) = True.
Proof. exact (EQ_MP (@lem1260111 m n) (@lem1260110 m n)). Qed.
Lemma lem1260420 (A : nat) (d : nat) (n : nat) (C : nat) : (term134 A d n C) = True.
Proof. exact (@lem1260419 (Nat.mul A n) (term95 d n C)). Qed.
Lemma lem1260421 (A : nat) (d : nat) (n : nat) (C : nat) : (term133 A d n C) = True.
Proof. exact (TRANS (@lem1260417 A d n C) (@lem1260420 A d n C)). Qed.
Lemma lem1260422 (A : nat) (d : nat) (C : nat) : (term135 A d C) = term136.
Proof. exact (fun_ext (fun n : nat => @lem1260421 A d n C)). Qed.
Lemma lem1260423 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1260424 (A : nat) (d : nat) (C : nat) : (term124 A d C) = term137.
Proof. exact (MK_COMB (@lem1260423) (@lem1260422 A d C)). Qed.
Lemma lem1260426 {A : Type'} (t : Prop) : (term138 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1260427 (t : Prop) : (term139 t) = t.
Proof. exact (@lem1260426 nat t). Qed.
Lemma lem1260428 : term137 = True.
Proof. exact (@lem1260427 True). Qed.
Lemma lem1260429 (A : nat) (d : nat) (C : nat) : (term124 A d C) = True.
Proof. exact (TRANS (@lem1260424 A d C) (@lem1260428)). Qed.
Lemma lem1260430 (A : nat) (d : nat) (C : nat) : True = (term124 A d C).
Proof. exact (SYM (@lem1260429 A d C)). Qed.
Lemma lem1260431 (A : nat) (d : nat) (C : nat) : term124 A d C.
Proof. exact (EQ_MP (@lem1260430 A d C) (@lem0)). Qed.
Lemma lem1260432 (C : nat) (B : nat) (A : nat) (d : nat) (h1 : B = (Nat.add A d)) : term80 A B C.
Proof. exact (EQ_MP (@lem1260398 C B A d h1) (@lem1260431 A d C)). Qed.
Lemma lem1260433 (C : nat) (A : nat) (B : nat) (h1 : Peano.le A B) : term80 A B C.
Proof. exact (ex_elim (@lem1260384 A B h1) (fun d : nat => fun h0 : term140 B A d => @lem1260432 C B A d h0)). Qed.
Lemma lem1260434 (A : nat) (B : nat) (C : nat) : term141 A B C.
Proof. exact (fun h0 : Peano.le A B => @lem1260433 C A B h0). Qed.
Lemma lem1260435 (A : nat) (B : nat) (C : nat) : term142 A B C.
Proof. exact (conj (@lem1260373 C A B) (@lem1260434 A B C)). Qed.
Lemma lem1260436 (C : nat) (A : nat) (B : nat) : (term142 A B C) = ((term80 A B C) = (Peano.le A B)).
Proof. exact (@lem32 (term80 A B C) (Peano.le A B)). Qed.
Lemma lem1260437 (C : nat) (A : nat) (B : nat) : (term80 A B C) = (Peano.le A B).
Proof. exact (EQ_MP (@lem1260436 C A B) (@lem1260435 A B C)). Qed.
Lemma lem1260442 (A : nat) (B : nat) : term143 A B.
Proof. exact (fun C : nat => @lem1260437 C A B). Qed.
Lemma lem1260447 (A : nat) : term144 A.
Proof. exact (fun B : nat => @lem1260442 A B). Qed.
Lemma lem1260452 : term145.
Proof. exact (fun A : nat => @lem1260447 A). Qed.
