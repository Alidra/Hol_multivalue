Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1068183_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import sum_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1068090 {A B : Type'} (OUTL' : type7 A B) (h1 : term0 A B OUTL') : term0 A B OUTL'.
Proof. exact (h1). Qed.
Lemma lem1068091 {A B : Type'} (x : A) (OUTL' : type7 A B) (h1 : term0 A B OUTL') : term1 A B OUTL' x.
Proof. exact (@lem1068090 A B OUTL' h1 x). Qed.
Lemma lem1068092 {A B : Type'} (OUTL' : type7 A B) (x : A) : (term1 A B OUTL' x) = ((term2 A B OUTL' x) = x).
Proof. exact (eq_refl (term1 A B OUTL' x)). Qed.
Lemma lem1068093 {A B : Type'} (x : A) (OUTL' : type7 A B) (h1 : term0 A B OUTL') : (term2 A B OUTL' x) = x.
Proof. exact (EQ_MP (@lem1068092 A B OUTL' x) (@lem1068091 A B x OUTL' h1)). Qed.
Lemma lem1068094 {A B : Type'} (OUTL' : type7 A B) (h1 : term0 A B OUTL') : term0 A B OUTL'.
Proof. exact (fun x : A => @lem1068093 A B x OUTL' h1). Qed.
Lemma lem1068095 {A B : Type'} (OUTL' : type7 A B) (h1 : term0 A B OUTL') : term0 A B OUTL'.
Proof. exact (h1). Qed.
Lemma lem1068096 {A B : Type'} (OUTL' : type7 A B) : (term0 A B OUTL') = (term0 A B OUTL').
Proof. exact (prop_ext (fun h1 : term0 A B OUTL' => @lem1068094 A B OUTL' h1) (fun h1 : term0 A B OUTL' => @lem1068095 A B OUTL' h1)). Qed.
Lemma lem1068097 {A B : Type'} (OUTL' : type7 A B) (h1 : term0 A B OUTL') : term0 A B OUTL'.
Proof. exact (EQ_MP (@lem1068096 A B OUTL') (@lem1068095 A B OUTL' h1)). Qed.
Lemma lem1068098 {A B Z : Type'} (INL' : A -> Z) : term3 A B Z INL'.
Proof. exact (@lem1068060 A B Z INL'). Qed.
Lemma lem1068099 {A B Z : Type'} (INL' : A -> Z) : (term3 A B Z INL') = (term4 A B Z INL').
Proof. exact (eq_refl (term3 A B Z INL')). Qed.
Lemma lem1068100 {A B Z : Type'} (INL' : A -> Z) : term4 A B Z INL'.
Proof. exact (EQ_MP (@lem1068099 A B Z INL') (@lem1068098 A B Z INL')). Qed.
Lemma lem1068101 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : term5 A B Z INL' INR'.
Proof. exact (@lem1068100 A B Z INL' INR'). Qed.
Lemma lem1068102 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : (term5 A B Z INL' INR') = (term6 A B Z INL' INR').
Proof. exact (eq_refl (term5 A B Z INL' INR')). Qed.
Lemma lem1068103 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : term6 A B Z INL' INR'.
Proof. exact (EQ_MP (@lem1068102 A B Z INL' INR') (@lem1068101 A B Z INL' INR')). Qed.
Lemma lem1068104 {A B : Type'} (INL' : A -> A) (INR' : B -> A) : term7 A B INL' INR'.
Proof. exact (@lem1068103 A B A INL' INR'). Qed.
Lemma lem1068105 {A B : Type'} (INR' : B -> A) : term8 A B INR'.
Proof. exact (@lem1068104 A B (term9 A) INR'). Qed.
Lemma lem1068106 {A : Type'} (a : A) : (term10 A a) = a.
Proof. exact (eq_refl (term10 A a)). Qed.
Lemma lem1068107 {A B : Type'} (fn : type7 A B) (a : A) : (term11 A B fn a) = (term11 A B fn a).
Proof. exact (eq_refl (term11 A B fn a)). Qed.
Lemma lem1068108 {A B : Type'} (fn : type7 A B) (a : A) : ((term2 A B fn a) = (term10 A a)) = ((term2 A B fn a) = a).
Proof. exact (MK_COMB (@lem1068107 A B fn a) (@lem1068106 A a)). Qed.
Lemma lem1068109 {A B : Type'} (fn : type7 A B) : (term12 A B fn) = (term13 A B fn).
Proof. exact (fun_ext (fun a : A => @lem1068108 A B fn a)). Qed.
Lemma lem1068110 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1068111 {A B : Type'} (fn : type7 A B) : (term14 A B fn) = (term0 A B fn).
Proof. exact (MK_COMB (@lem1068110 A) (@lem1068109 A B fn)). Qed.
Lemma lem1068112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1068113 {A B : Type'} (fn : type7 A B) : (term15 A B fn) = (term16 A B fn).
Proof. exact (MK_COMB (@lem1068112) (@lem1068111 A B fn)). Qed.
Lemma lem1068114 {A B : Type'} (fn : type7 A B) (INR' : B -> A) : (term17 A B fn INR') = (term17 A B fn INR').
Proof. exact (eq_refl (term17 A B fn INR')). Qed.
Lemma lem1068115 {A B : Type'} (fn : type7 A B) (INR' : B -> A) : (term18 A B fn INR') = (term19 A B fn INR').
Proof. exact (MK_COMB (@lem1068113 A B fn) (@lem1068114 A B fn INR')). Qed.
Lemma lem1068116 {A B : Type'} (INR' : B -> A) : (term20 A B INR') = (term21 A B INR').
Proof. exact (fun_ext (fun fn : type7 A B => @lem1068115 A B fn INR')). Qed.
Lemma lem1068117 {A B : Type'} : (@ex ((Datatypes.sum A B) -> A)) = (@ex ((Datatypes.sum A B) -> A)).
Proof. exact (eq_refl (@ex ((Datatypes.sum A B) -> A))). Qed.
Lemma lem1068118 {A B : Type'} (INR' : B -> A) : (term8 A B INR') = (term22 A B INR').
Proof. exact (MK_COMB (@lem1068117 A B) (@lem1068116 A B INR')). Qed.
Lemma lem1068119 {A B : Type'} (INR' : B -> A) : term22 A B INR'.
Proof. exact (EQ_MP (@lem1068118 A B INR') (@lem1068105 A B INR')). Qed.
Lemma lem1068120 {A B : Type'} (OUTL' : type7 A B) (INR' : B -> A) (h1 : term19 A B OUTL' INR') : term19 A B OUTL' INR'.
Proof. exact (h1). Qed.
Lemma lem1068122 {A B : Type'} (OUTL' : type7 A B) (INR' : B -> A) (h1 : term19 A B OUTL' INR') : term0 A B OUTL'.
Proof. exact (proj1 (@lem1068120 A B OUTL' INR' h1)). Qed.
Lemma lem1068123 {A B : Type'} (OUTL' : type7 A B) (INR' : B -> A) (h1 : term19 A B OUTL' INR') : term23 A B.
Proof. exact (ex_intro (term24 A B) OUTL' (@lem1068122 A B OUTL' INR' h1)). Qed.
Lemma lem1068124 {A B : Type'} (INR' : B -> A) (h1 : term22 A B INR') : term22 A B INR'.
Proof. exact (h1). Qed.
Lemma lem1068125 {A B : Type'} (INR' : B -> A) (h1 : term22 A B INR') : term23 A B.
Proof. exact (ex_elim (@lem1068124 A B INR' h1) (fun OUTL' : type7 A B => fun h0 : term21 A B INR' OUTL' => @lem1068123 A B OUTL' INR' h0)). Qed.
Lemma lem1068126 {A B : Type'} (INR' : B -> A) : (term22 A B INR') = (term23 A B).
Proof. exact (prop_ext (fun h1 : term22 A B INR' => @lem1068125 A B INR' h1) (fun h1 : term23 A B => @lem1068119 A B INR')). Qed.
Lemma lem1068127 {A B : Type'} : term23 A B.
Proof. exact (EQ_MP (@lem1068126 A B (@el (B -> A))) (@lem1068119 A B (@el (B -> A)))). Qed.
Lemma lem1068128 {A B : Type'} (OUTL' : type7 A B) (h1 : term0 A B OUTL') : term23 A B.
Proof. exact (ex_intro (term24 A B) OUTL' (@lem1068097 A B OUTL' h1)). Qed.
Lemma lem1068129 {A B : Type'} (h1 : term23 A B) : term23 A B.
Proof. exact (h1). Qed.
Lemma lem1068130 {A B : Type'} (h1 : term23 A B) : term23 A B.
Proof. exact (ex_elim (@lem1068129 A B h1) (fun OUTL' : type7 A B => fun h0 : term24 A B OUTL' => @lem1068128 A B OUTL' h0)). Qed.
Lemma lem1068131 {A B : Type'} : (term23 A B) = (term23 A B).
Proof. exact (prop_ext (fun h1 : term23 A B => @lem1068130 A B h1) (fun h1 : term23 A B => @lem1068127 A B)). Qed.
Lemma lem1068132 {A B : Type'} : term23 A B.
Proof. exact (EQ_MP (@lem1068131 A B) (@lem1068127 A B)). Qed.
Lemma lem1068135 {A B : Type'} (OUTL' : type7 A B) (h1 : term0 A B OUTL') : term0 A B OUTL'.
Proof. exact (h1). Qed.
Lemma lem1068136 {A B : Type'} (OUTL' : type7 A B) (h1 : term0 A B OUTL') : term23 A B.
Proof. exact (ex_intro (term24 A B) OUTL' (@lem1068135 A B OUTL' h1)). Qed.
Lemma lem1068137 {A B : Type'} (h1 : term23 A B) : term23 A B.
Proof. exact (h1). Qed.
Lemma lem1068138 {A B : Type'} (h1 : term23 A B) : term23 A B.
Proof. exact (ex_elim (@lem1068137 A B h1) (fun OUTL' : type7 A B => fun h0 : term24 A B OUTL' => @lem1068136 A B OUTL' h0)). Qed.
Lemma lem1068139 {A B : Type'} : (term23 A B) = (term23 A B).
Proof. exact (prop_ext (fun h1 : term23 A B => @lem1068138 A B h1) (fun h1 : term23 A B => @lem1068132 A B)). Qed.
Lemma lem1068140 {A B : Type'} : term23 A B.
Proof. exact (EQ_MP (@lem1068139 A B) (@lem1068132 A B)). Qed.
Lemma lem1068141 {A B : Type'} : term25 A B.
Proof. exact (fun _17486 : type1673 => @lem1068140 A B). Qed.
Lemma lem1068142 {A B : Type'} (P : type1413 A B) : term26 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1068143 {A B : Type'} (P : type1413 A B) : (term26 A B P) = ((term27 A B P) = (term28 A B P)).
Proof. exact (eq_refl (term26 A B P)). Qed.
Lemma lem1068146 {A B : Type'} (P : type1413 A B) : (term27 A B P) = (term28 A B P).
Proof. exact (EQ_MP (@lem1068143 A B P) (@lem1068142 A B P)). Qed.
Lemma lem1068147 {A B : Type'} (P : type1279 A B) : (term29 A B P) = (term30 A B P).
Proof. exact (@lem1068146 type1673 (type7 A B) P). Qed.
Lemma lem1068148 {A B : Type'} : (term31 A B) = (term32 A B).
Proof. exact (@lem1068147 A B (term33 A B)). Qed.
Lemma lem1068149 {A B : Type'} (_17486 : type1673) : (term34 A B _17486) = (term24 A B).
Proof. exact (eq_refl (term34 A B _17486)). Qed.
Lemma lem1068150 {A B : Type'} (OUTL' : type7 A B) : OUTL' = OUTL'.
Proof. exact (eq_refl OUTL'). Qed.
Lemma lem1068151 {A B : Type'} (_17486 : type1673) (OUTL' : type7 A B) : (term35 A B _17486 OUTL') = (term36 A B OUTL').
Proof. exact (MK_COMB (@lem1068149 A B _17486) (@lem1068150 A B OUTL')). Qed.
Lemma lem1068152 {A B : Type'} (OUTL' : type7 A B) : (term36 A B OUTL') = (term0 A B OUTL').
Proof. exact (eq_refl (term36 A B OUTL')). Qed.
Lemma lem1068153 {A B : Type'} (_17486 : type1673) (OUTL' : type7 A B) : (term35 A B _17486 OUTL') = (term0 A B OUTL').
Proof. exact (TRANS (@lem1068151 A B _17486 OUTL') (@lem1068152 A B OUTL')). Qed.
Lemma lem1068154 {A B : Type'} (_17486 : type1673) : (term37 A B _17486) = (term24 A B).
Proof. exact (fun_ext (fun OUTL' : type7 A B => @lem1068153 A B _17486 OUTL')). Qed.
Lemma lem1068155 {A B : Type'} : (@ex ((Datatypes.sum A B) -> A)) = (@ex ((Datatypes.sum A B) -> A)).
Proof. exact (eq_refl (@ex ((Datatypes.sum A B) -> A))). Qed.
Lemma lem1068156 {A B : Type'} (_17486 : type1673) : (term38 A B _17486) = (term23 A B).
Proof. exact (MK_COMB (@lem1068155 A B) (@lem1068154 A B _17486)). Qed.
Lemma lem1068157 {A B : Type'} : (term39 A B) = (term40 A B).
Proof. exact (fun_ext (fun _17486 : type1673 => @lem1068156 A B _17486)). Qed.
Lemma lem1068158 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1068159 {A B : Type'} : (term31 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem1068158) (@lem1068157 A B)). Qed.
Lemma lem1068160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1068161 {A B : Type'} : (term41 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem1068160) (@lem1068159 A B)). Qed.
Lemma lem1068162 {A B : Type'} (_17486 : type1673) : (term34 A B _17486) = (term24 A B).
Proof. exact (eq_refl (term34 A B _17486)). Qed.
Lemma lem1068163 {A B : Type'} (OUTL' : type1277 A B) (_17486 : type1673) : (OUTL' _17486) = (OUTL' _17486).
Proof. exact (eq_refl (OUTL' _17486)). Qed.
Lemma lem1068164 {A B : Type'} (OUTL' : type1277 A B) (_17486 : type1673) : (term43 A B OUTL' _17486) = (term44 A B OUTL' _17486).
Proof. exact (MK_COMB (@lem1068162 A B _17486) (@lem1068163 A B OUTL' _17486)). Qed.
Lemma lem1068165 {A B : Type'} (OUTL' : type1277 A B) (_17486 : type1673) : (term44 A B OUTL' _17486) = (term45 A B OUTL' _17486).
Proof. exact (eq_refl (term44 A B OUTL' _17486)). Qed.
Lemma lem1068166 {A B : Type'} (OUTL' : type1277 A B) (_17486 : type1673) : (term43 A B OUTL' _17486) = (term45 A B OUTL' _17486).
Proof. exact (TRANS (@lem1068164 A B OUTL' _17486) (@lem1068165 A B OUTL' _17486)). Qed.
Lemma lem1068167 {A B : Type'} (OUTL' : type1277 A B) : (term46 A B OUTL') = (term47 A B OUTL').
Proof. exact (fun_ext (fun _17486 : type1673 => @lem1068166 A B OUTL' _17486)). Qed.
Lemma lem1068168 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1068169 {A B : Type'} (OUTL' : type1277 A B) : (term48 A B OUTL') = (term49 A B OUTL').
Proof. exact (MK_COMB (@lem1068168) (@lem1068167 A B OUTL')). Qed.
Lemma lem1068170 {A B : Type'} : (term50 A B) = (term51 A B).
Proof. exact (fun_ext (fun OUTL' : type1277 A B => @lem1068169 A B OUTL')). Qed.
Lemma lem1068171 {A B : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A)) = (@ex ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A))). Qed.
Lemma lem1068172 {A B : Type'} : (term32 A B) = (term52 A B).
Proof. exact (MK_COMB (@lem1068171 A B) (@lem1068170 A B)). Qed.
Lemma lem1068173 {A B : Type'} : ((term31 A B) = (term32 A B)) = ((term25 A B) = (term52 A B)).
Proof. exact (MK_COMB (@lem1068161 A B) (@lem1068172 A B)). Qed.
Lemma lem1068174 {A B : Type'} : (term25 A B) = (term52 A B).
Proof. exact (EQ_MP (@lem1068173 A B) (@lem1068148 A B)). Qed.
Lemma lem1068175 {A B : Type'} : term52 A B.
Proof. exact (EQ_MP (@lem1068174 A B) (@lem1068141 A B)). Qed.
Lemma lem1068177 {A : Type'} : (@ex A) = (term53 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1068178 {A B : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> A)) = (term54 A B).
Proof. exact (@lem1068177 (type1277 A B)). Qed.
Lemma lem1068179 {A B : Type'} : (term51 A B) = (term51 A B).
Proof. exact (eq_refl (term51 A B)). Qed.
Lemma lem1068180 {A B : Type'} : (term52 A B) = (term55 A B).
Proof. exact (MK_COMB (@lem1068178 A B) (@lem1068179 A B)). Qed.
Lemma lem1068181 {A B : Type'} : (term55 A B) = (term56 A B).
Proof. exact (eq_refl (term55 A B)). Qed.
Lemma lem1068182 {A B : Type'} : (term52 A B) = (term56 A B).
Proof. exact (TRANS (@lem1068180 A B) (@lem1068181 A B)). Qed.
Lemma lem1068183 {A B : Type'} : term56 A B.
Proof. exact (EQ_MP (@lem1068182 A B) (@lem1068175 A B)). Qed.
