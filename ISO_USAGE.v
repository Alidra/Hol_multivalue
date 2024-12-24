Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ISO_USAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import ISO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Lemma lem1076904 {A B : Type'} (g : B -> A) : term0 A B g.
Proof. exact (@lem1075149 A B g). Qed.
Lemma lem1076905 {A B : Type'} (g : B -> A) : (term0 A B g) = (term1 A B g).
Proof. exact (eq_refl (term0 A B g)). Qed.
Lemma lem1076906 {A B : Type'} (g : B -> A) : term1 A B g.
Proof. exact (EQ_MP (@lem1076905 A B g) (@lem1076904 A B g)). Qed.
Lemma lem1076907 {A B : Type'} (g : B -> A) (f : A -> B) : term2 A B g f.
Proof. exact (@lem1076906 A B g f). Qed.
Lemma lem1076908 {A B : Type'} (g : B -> A) (f : A -> B) : (term2 A B g f) = ((@ExtensionalityFacts.is_inverse A B f g) = (term3 A B g f)).
Proof. exact (eq_refl (term2 A B g f)). Qed.
Lemma lem1076913 {A B : Type'} (g : B -> A) (f : A -> B) : (@ExtensionalityFacts.is_inverse A B f g) = (term3 A B g f).
Proof. exact (EQ_MP (@lem1076908 A B g f) (@lem1076907 A B g f)). Qed.
Lemma lem1076914 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (@ExtensionalityFacts.is_inverse _24635 _24632 f g) = (term4 _24632 _24635 g f).
Proof. exact (@lem1076913 _24635 _24632 g f). Qed.
Lemma lem1076933 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1076934 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term5 _24632 _24635 f g) = (term6 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1076933) (@lem1076914 _24632 _24635 g f)). Qed.
Lemma lem1076991 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term7 _24632 _24635 g f) = (term7 _24632 _24635 g f).
Proof. exact (eq_refl (term7 _24632 _24635 g f)). Qed.
Lemma lem1076992 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term8 _24632 _24635 g f) = (term9 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1076934 _24632 _24635 g f) (@lem1076991 _24632 _24635 g f)). Qed.
Lemma lem1076995 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term9 _24632 _24635 g f) = (term8 _24632 _24635 g f).
Proof. exact (SYM (@lem1076992 _24632 _24635 g f)). Qed.
Lemma lem1076997 (p : Prop) : p = (term10 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1076998 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term9 _24632 _24635 g f) = (term11 _24632 _24635 g f).
Proof. exact (@lem1076997 (term9 _24632 _24635 g f)). Qed.
Lemma lem1076999 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term11 _24632 _24635 g f) = (term9 _24632 _24635 g f).
Proof. exact (SYM (@lem1076998 _24632 _24635 g f)). Qed.
Lemma lem1077000 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term12 _24632 _24635 g f) : term12 _24632 _24635 g f.
Proof. exact (h1). Qed.
Lemma lem1077003 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term11 _24632 _24635 g f) : term11 _24632 _24635 g f.
Proof. exact (h1). Qed.
Lemma lem1077004 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term13 _24632 _24635 g f.
Proof. exact (fun h0 : term11 _24632 _24635 g f => @lem1077003 _24632 _24635 g f h0). Qed.
Lemma lem1077005 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term13 _24632 _24635 g f) : term13 _24632 _24635 g f.
Proof. exact (h1). Qed.
Lemma lem1077006 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term11 _24632 _24635 g f) : term11 _24632 _24635 g f.
Proof. exact (h1). Qed.
Lemma lem1077007 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term11 _24632 _24635 g f) (h2 : term13 _24632 _24635 g f) : term11 _24632 _24635 g f.
Proof. exact (@lem1077005 _24632 _24635 g f h2 (@lem1077006 _24632 _24635 g f h1)). Qed.
Lemma lem1077008 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term11 _24632 _24635 g f) : term14 _24632 _24635 g f.
Proof. exact (fun h0 : term13 _24632 _24635 g f => @lem1077007 _24632 _24635 g f h1 h0). Qed.
Lemma lem1077009 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term13 _24632 _24635 g f) : term13 _24632 _24635 g f.
Proof. exact (h1). Qed.
Lemma lem1077010 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term11 _24632 _24635 g f) (h2 : term13 _24632 _24635 g f) : term11 _24632 _24635 g f.
Proof. exact (@lem1077008 _24632 _24635 g f h1 (@lem1077009 _24632 _24635 g f h2)). Qed.
Lemma lem1077011 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term13 _24632 _24635 g f) : term13 _24632 _24635 g f.
Proof. exact (fun h0 : term11 _24632 _24635 g f => @lem1077010 _24632 _24635 g f h0 h1). Qed.
Lemma lem1077012 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term15 _24632 _24635 g f.
Proof. exact (fun h0 : term13 _24632 _24635 g f => @lem1077011 _24632 _24635 g f h0). Qed.
Lemma lem1077015 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term13 _24632 _24635 g f.
Proof. exact (@lem1077012 _24632 _24635 g f (@lem1077004 _24632 _24635 g f)). Qed.
Lemma lem1077016 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term13 _24632 _24635 g f.
Proof. exact (@lem1077015 _24632 _24635 g f). Qed.
Lemma lem1077026 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1077027 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term11 _24632 _24635 g f) = (term16 _24632 _24635 g f).
Proof. exact (@lem1077026 (term12 _24632 _24635 g f)). Qed.
Lemma lem1077029 (t : Prop) : (term17 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1077030 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term16 _24632 _24635 g f) = (term9 _24632 _24635 g f).
Proof. exact (@lem1077029 (term9 _24632 _24635 g f)). Qed.
Lemma lem1077033 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term11 _24632 _24635 g f) = (term9 _24632 _24635 g f).
Proof. exact (TRANS (@lem1077027 _24632 _24635 g f) (@lem1077030 _24632 _24635 g f)). Qed.
Lemma lem1077080 {_24632 _24635 : Type'} (f : _24635 -> _24632) : (term18 _24632 _24635 f) = (term19 _24632 _24635 f).
Proof. exact (fun_ext (fun g : _24632 -> _24635 => @lem1077033 _24632 _24635 g f)). Qed.
Lemma lem1077081 {_24632 _24635 : Type'} : (@all (_24632 -> _24635)) = (@all (_24632 -> _24635)).
Proof. exact (eq_refl (@all (_24632 -> _24635))). Qed.
Lemma lem1077082 {_24632 _24635 : Type'} (f : _24635 -> _24632) : (term20 _24632 _24635 f) = (term21 _24632 _24635 f).
Proof. exact (MK_COMB (@lem1077081 _24632 _24635) (@lem1077080 _24632 _24635 f)). Qed.
Lemma lem1077087 {_24632 _24635 : Type'} : (term22 _24632 _24635) = (term23 _24632 _24635).
Proof. exact (fun_ext (fun f : _24635 -> _24632 => @lem1077082 _24632 _24635 f)). Qed.
Lemma lem1077088 {_24632 _24635 : Type'} : (@all (_24635 -> _24632)) = (@all (_24635 -> _24632)).
Proof. exact (eq_refl (@all (_24635 -> _24632))). Qed.
Lemma lem1077097 {_24632 _24635 : Type'} : (term24 _24632 _24635) = (term25 _24632 _24635).
Proof. exact (MK_COMB (@lem1077088 _24632 _24635) (@lem1077087 _24632 _24635)). Qed.
Lemma lem1077102 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : ((a = (g b)) = ((f a) = b)) = ((a = (g b)) = ((f a) = b)).
Proof. exact (eq_refl ((a = (g b)) = ((f a) = b))). Qed.
Lemma lem1077103 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term26 _24632 _24635 g f a) = (term26 _24632 _24635 g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1077102 _24632 _24635 g f a b)). Qed.
Lemma lem1077104 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1077105 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term27 _24632 _24635 g f a) = (term27 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077104 _24632) (@lem1077103 _24632 _24635 g f a)). Qed.
Lemma lem1077106 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term28 _24632 _24635 g f) = (term28 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1077105 _24632 _24635 g f a)). Qed.
Lemma lem1077107 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1077108 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term29 _24632 _24635 g f) = (term29 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077107 _24635) (@lem1077106 _24632 _24635 g f)). Qed.
Lemma lem1077109 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term30 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term30 _24632 _24635 P g x)). Qed.
Lemma lem1077110 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term31 _24632 _24635 P g) = (term31 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077109 _24632 _24635 P g x)). Qed.
Lemma lem1077111 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1077112 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term32 _24632 _24635 P g) = (term32 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077111 _24632) (@lem1077110 _24632 _24635 P g)). Qed.
Lemma lem1077113 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1077114 {_24635 : Type'} (P : _24635 -> Prop) : (term33 _24635 P) = (term33 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1077113 _24635 P x)). Qed.
Lemma lem1077115 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1077116 {_24635 : Type'} (P : _24635 -> Prop) : (term34 _24635 P) = (term34 _24635 P).
Proof. exact (MK_COMB (@lem1077115 _24635) (@lem1077114 _24635 P)). Qed.
Lemma lem1077117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1077118 {_24635 : Type'} (P : _24635 -> Prop) : (term35 _24635 P) = (term35 _24635 P).
Proof. exact (MK_COMB (@lem1077117) (@lem1077116 _24635 P)). Qed.
Lemma lem1077119 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : ((term34 _24635 P) = (term32 _24632 _24635 P g)) = ((term34 _24635 P) = (term32 _24632 _24635 P g)).
Proof. exact (MK_COMB (@lem1077118 _24635 P) (@lem1077112 _24632 _24635 P g)). Qed.
Lemma lem1077120 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term36 _24632 _24635 g) = (term36 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077119 _24632 _24635 P g)). Qed.
Lemma lem1077121 {_24635 : Type'} : (@all (_24635 -> Prop)) = (@all (_24635 -> Prop)).
Proof. exact (eq_refl (@all (_24635 -> Prop))). Qed.
Lemma lem1077122 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term37 _24632 _24635 g) = (term37 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077121 _24635) (@lem1077120 _24632 _24635 g)). Qed.
Lemma lem1077123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1077124 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term38 _24632 _24635 g) = (term38 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077123) (@lem1077122 _24632 _24635 g)). Qed.
Lemma lem1077125 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term39 _24632 _24635 g f) = (term39 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077124 _24632 _24635 g) (@lem1077108 _24632 _24635 g f)). Qed.
Lemma lem1077126 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term30 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term30 _24632 _24635 P g x)). Qed.
Lemma lem1077127 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term31 _24632 _24635 P g) = (term31 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077126 _24632 _24635 P g x)). Qed.
Lemma lem1077128 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1077129 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term40 _24632 _24635 P g) = (term40 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077128 _24632) (@lem1077127 _24632 _24635 P g)). Qed.
Lemma lem1077130 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1077131 {_24635 : Type'} (P : _24635 -> Prop) : (term33 _24635 P) = (term33 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1077130 _24635 P x)). Qed.
Lemma lem1077132 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1077133 {_24635 : Type'} (P : _24635 -> Prop) : (term41 _24635 P) = (term41 _24635 P).
Proof. exact (MK_COMB (@lem1077132 _24635) (@lem1077131 _24635 P)). Qed.
Lemma lem1077134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1077135 {_24635 : Type'} (P : _24635 -> Prop) : (term42 _24635 P) = (term42 _24635 P).
Proof. exact (MK_COMB (@lem1077134) (@lem1077133 _24635 P)). Qed.
Lemma lem1077136 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : ((term41 _24635 P) = (term40 _24632 _24635 P g)) = ((term41 _24635 P) = (term40 _24632 _24635 P g)).
Proof. exact (MK_COMB (@lem1077135 _24635 P) (@lem1077129 _24632 _24635 P g)). Qed.
Lemma lem1077137 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term43 _24632 _24635 g) = (term43 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077136 _24632 _24635 P g)). Qed.
Lemma lem1077138 {_24635 : Type'} : (@all (_24635 -> Prop)) = (@all (_24635 -> Prop)).
Proof. exact (eq_refl (@all (_24635 -> Prop))). Qed.
Lemma lem1077139 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term44 _24632 _24635 g) = (term44 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077138 _24635) (@lem1077137 _24632 _24635 g)). Qed.
Lemma lem1077140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1077141 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term45 _24632 _24635 g) = (term45 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077140) (@lem1077139 _24632 _24635 g)). Qed.
Lemma lem1077142 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term7 _24632 _24635 g f) = (term7 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077141 _24632 _24635 g) (@lem1077125 _24632 _24635 g f)). Qed.
Lemma lem1077143 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (y : _24635) : ((term46 _24632 _24635 g f y) = y) = ((term46 _24632 _24635 g f y) = y).
Proof. exact (eq_refl ((term46 _24632 _24635 g f y) = y)). Qed.
Lemma lem1077144 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term47 _24632 _24635 g f) = (term47 _24632 _24635 g f).
Proof. exact (fun_ext (fun y : _24635 => @lem1077143 _24632 _24635 g f y)). Qed.
Lemma lem1077145 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1077146 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term48 _24632 _24635 g f) = (term48 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077145 _24635) (@lem1077144 _24632 _24635 g f)). Qed.
Lemma lem1077147 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) (x : _24632) : ((term49 _24632 _24635 f g x) = x) = ((term49 _24632 _24635 f g x) = x).
Proof. exact (eq_refl ((term49 _24632 _24635 f g x) = x)). Qed.
Lemma lem1077148 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term50 _24632 _24635 f g) = (term50 _24632 _24635 f g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077147 _24632 _24635 f g x)). Qed.
Lemma lem1077149 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1077150 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term51 _24632 _24635 f g) = (term51 _24632 _24635 f g).
Proof. exact (MK_COMB (@lem1077149 _24632) (@lem1077148 _24632 _24635 f g)). Qed.
Lemma lem1077151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1077152 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term52 _24632 _24635 f g) = (term52 _24632 _24635 f g).
Proof. exact (MK_COMB (@lem1077151) (@lem1077150 _24632 _24635 f g)). Qed.
Lemma lem1077153 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term4 _24632 _24635 g f) = (term4 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077152 _24632 _24635 f g) (@lem1077146 _24632 _24635 g f)). Qed.
Lemma lem1077154 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1077155 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term6 _24632 _24635 g f) = (term6 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077154) (@lem1077153 _24632 _24635 g f)). Qed.
Lemma lem1077156 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term9 _24632 _24635 g f) = (term9 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077155 _24632 _24635 g f) (@lem1077142 _24632 _24635 g f)). Qed.
Lemma lem1077157 {_24632 _24635 : Type'} (f : _24635 -> _24632) : (term19 _24632 _24635 f) = (term19 _24632 _24635 f).
Proof. exact (fun_ext (fun g : _24632 -> _24635 => @lem1077156 _24632 _24635 g f)). Qed.
Lemma lem1077158 {_24632 _24635 : Type'} : (@all (_24632 -> _24635)) = (@all (_24632 -> _24635)).
Proof. exact (eq_refl (@all (_24632 -> _24635))). Qed.
Lemma lem1077159 {_24632 _24635 : Type'} (f : _24635 -> _24632) : (term21 _24632 _24635 f) = (term21 _24632 _24635 f).
Proof. exact (MK_COMB (@lem1077158 _24632 _24635) (@lem1077157 _24632 _24635 f)). Qed.
Lemma lem1077160 {_24632 _24635 : Type'} : (term23 _24632 _24635) = (term23 _24632 _24635).
Proof. exact (fun_ext (fun f : _24635 -> _24632 => @lem1077159 _24632 _24635 f)). Qed.
Lemma lem1077161 {_24632 _24635 : Type'} : (@all (_24635 -> _24632)) = (@all (_24635 -> _24632)).
Proof. exact (eq_refl (@all (_24635 -> _24632))). Qed.
Lemma lem1077162 {_24632 _24635 : Type'} : (term25 _24632 _24635) = (term25 _24632 _24635).
Proof. exact (MK_COMB (@lem1077161 _24632 _24635) (@lem1077160 _24632 _24635)). Qed.
Lemma lem1077245 {_24632 _24635 : Type'} : (term24 _24632 _24635) = (term25 _24632 _24635).
Proof. exact (TRANS (@lem1077097 _24632 _24635) (@lem1077162 _24632 _24635)). Qed.
Lemma lem1077246 {_24632 _24635 : Type'} : (term25 _24632 _24635) = (term24 _24632 _24635).
Proof. exact (SYM (@lem1077245 _24632 _24635)). Qed.
Lemma lem1077247 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term4 _24632 _24635 g f.
Proof. exact (h1). Qed.
Lemma lem1077249 (p : Prop) : p = (term10 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1077250 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term7 _24632 _24635 g f) = (term53 _24632 _24635 g f).
Proof. exact (@lem1077249 (term7 _24632 _24635 g f)). Qed.
Lemma lem1077251 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term53 _24632 _24635 g f) = (term7 _24632 _24635 g f).
Proof. exact (SYM (@lem1077250 _24632 _24635 g f)). Qed.
Lemma lem1077252 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term54 _24632 _24635 g f) : term54 _24632 _24635 g f.
Proof. exact (h1). Qed.
Lemma lem1077253 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) (x : _24632) : ((term49 _24632 _24635 f g x) = x) = ((term49 _24632 _24635 f g x) = x).
Proof. exact (eq_refl ((term49 _24632 _24635 f g x) = x)). Qed.
Lemma lem1077254 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term50 _24632 _24635 f g) = (term50 _24632 _24635 f g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077253 _24632 _24635 f g x)). Qed.
Lemma lem1077255 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1077256 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term51 _24632 _24635 f g) = (term51 _24632 _24635 f g).
Proof. exact (MK_COMB (@lem1077255 _24632) (@lem1077254 _24632 _24635 f g)). Qed.
Lemma lem1077257 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (y : _24635) : ((term46 _24632 _24635 g f y) = y) = ((term46 _24632 _24635 g f y) = y).
Proof. exact (eq_refl ((term46 _24632 _24635 g f y) = y)). Qed.
Lemma lem1077258 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term47 _24632 _24635 g f) = (term47 _24632 _24635 g f).
Proof. exact (fun_ext (fun y : _24635 => @lem1077257 _24632 _24635 g f y)). Qed.
Lemma lem1077259 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1077260 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term48 _24632 _24635 g f) = (term48 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077259 _24635) (@lem1077258 _24632 _24635 g f)). Qed.
Lemma lem1077261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1077262 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term52 _24632 _24635 f g) = (term52 _24632 _24635 f g).
Proof. exact (MK_COMB (@lem1077261) (@lem1077256 _24632 _24635 f g)). Qed.
Lemma lem1077275 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term4 _24632 _24635 g f) = (term4 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077262 _24632 _24635 f g) (@lem1077260 _24632 _24635 g f)). Qed.
Lemma lem1077276 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term4 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1077275 _24632 _24635 g f) (@lem1077247 _24632 _24635 g f h1)). Qed.
Lemma lem1077278 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1077279 {_24635 : Type'} (P : _24635 -> Prop) : (term55 _24635 P) = (term56 _24635 P).
Proof. exact (@lem18392 _24635 P). Qed.
Lemma lem1077280 {_24635 : Type'} (P : _24635 -> Prop) : (term57 _24635 P) = (term58 _24635 P).
Proof. exact (@lem1077279 _24635 (term33 _24635 P)). Qed.
Lemma lem1077281 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (term59 _24635 P x) = (P x).
Proof. exact (eq_refl (term59 _24635 P x)). Qed.
Lemma lem1077282 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1077284 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (term60 _24635 P x) = (term61 _24635 P x).
Proof. exact (MK_COMB (@lem1077282) (@lem1077281 _24635 P x)). Qed.
Lemma lem1077285 {_24635 : Type'} (P : _24635 -> Prop) : (term62 _24635 P) = (term63 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1077284 _24635 P x)). Qed.
Lemma lem1077286 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1077287 {_24635 : Type'} (P : _24635 -> Prop) : (term58 _24635 P) = (term56 _24635 P).
Proof. exact (MK_COMB (@lem1077286 _24635) (@lem1077285 _24635 P)). Qed.
Lemma lem1077288 {_24635 : Type'} (P : _24635 -> Prop) : (term57 _24635 P) = (term56 _24635 P).
Proof. exact (TRANS (@lem1077280 _24635 P) (@lem1077287 _24635 P)). Qed.
Lemma lem1077289 {_24635 : Type'} (P : _24635 -> Prop) : (term33 _24635 P) = (term33 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1077278 _24635 P x)). Qed.
Lemma lem1077290 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1077291 {_24635 : Type'} (P : _24635 -> Prop) : (term41 _24635 P) = (term41 _24635 P).
Proof. exact (MK_COMB (@lem1077290 _24635) (@lem1077289 _24635 P)). Qed.
Lemma lem1077293 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term30 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term30 _24632 _24635 P g x)). Qed.
Lemma lem1077294 {_24632 : Type'} (P : _24632 -> Prop) : (term55 _24632 P) = (term56 _24632 P).
Proof. exact (@lem18392 _24632 P). Qed.
Lemma lem1077295 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term64 _24632 _24635 P g) = (term65 _24632 _24635 P g).
Proof. exact (@lem1077294 _24632 (term31 _24632 _24635 P g)). Qed.
Lemma lem1077296 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term66 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term66 _24632 _24635 P g x)). Qed.
Lemma lem1077297 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1077299 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term67 _24632 _24635 P g x) = (term68 _24632 _24635 P g x).
Proof. exact (MK_COMB (@lem1077297) (@lem1077296 _24632 _24635 P g x)). Qed.
Lemma lem1077300 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term69 _24632 _24635 P g) = (term70 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077299 _24632 _24635 P g x)). Qed.
Lemma lem1077301 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1077302 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term65 _24632 _24635 P g) = (term71 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077301 _24632) (@lem1077300 _24632 _24635 P g)). Qed.
Lemma lem1077303 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term64 _24632 _24635 P g) = (term71 _24632 _24635 P g).
Proof. exact (TRANS (@lem1077295 _24632 _24635 P g) (@lem1077302 _24632 _24635 P g)). Qed.
Lemma lem1077304 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term31 _24632 _24635 P g) = (term31 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077293 _24632 _24635 P g x)). Qed.
Lemma lem1077305 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1077306 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term40 _24632 _24635 P g) = (term40 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077305 _24632) (@lem1077304 _24632 _24635 P g)). Qed.
Lemma lem1077307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1077308 {_24635 : Type'} (P : _24635 -> Prop) : (term72 _24635 P) = (term73 _24635 P).
Proof. exact (MK_COMB (@lem1077307) (@lem1077288 _24635 P)). Qed.
Lemma lem1077309 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term74 _24632 _24635 P g) = (term75 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077308 _24635 P) (@lem1077306 _24632 _24635 P g)). Qed.
Lemma lem1077310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1077311 {_24635 : Type'} (P : _24635 -> Prop) : (term76 _24635 P) = (term76 _24635 P).
Proof. exact (MK_COMB (@lem1077310) (@lem1077291 _24635 P)). Qed.
Lemma lem1077312 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term77 _24632 _24635 P g) = (term78 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077311 _24635 P) (@lem1077303 _24632 _24635 P g)). Qed.
Lemma lem1077313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077314 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term79 _24632 _24635 P g) = (term80 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077313) (@lem1077312 _24632 _24635 P g)). Qed.
Lemma lem1077315 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term81 _24632 _24635 P g) = (term82 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077314 _24632 _24635 P g) (@lem1077309 _24632 _24635 P g)). Qed.
Lemma lem1077316 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term83 _24632 _24635 P g) = (term81 _24632 _24635 P g).
Proof. exact (@lem17646 (term41 _24635 P) (term40 _24632 _24635 P g)). Qed.
Lemma lem1077317 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term83 _24632 _24635 P g) = (term82 _24632 _24635 P g).
Proof. exact (TRANS (@lem1077316 _24632 _24635 P g) (@lem1077315 _24632 _24635 P g)). Qed.
Lemma lem1077318 {_24635 : Type'} (P : type686 _24635) : (term84 _24635 P) = (term85 _24635 P).
Proof. exact (@lem18392 (_24635 -> Prop) P). Qed.
Lemma lem1077319 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term86 _24632 _24635 g) = (term87 _24632 _24635 g).
Proof. exact (@lem1077318 _24635 (term43 _24632 _24635 g)). Qed.
Lemma lem1077320 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term88 _24632 _24635 g P) = ((term41 _24635 P) = (term40 _24632 _24635 P g)).
Proof. exact (eq_refl (term88 _24632 _24635 g P)). Qed.
Lemma lem1077321 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1077322 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term89 _24632 _24635 g P) = (term83 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077321) (@lem1077320 _24632 _24635 P g)). Qed.
Lemma lem1077323 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term89 _24632 _24635 g P) = (term82 _24632 _24635 P g).
Proof. exact (TRANS (@lem1077322 _24632 _24635 P g) (@lem1077317 _24632 _24635 P g)). Qed.
Lemma lem1077324 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term90 _24632 _24635 g) = (term91 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077323 _24632 _24635 P g)). Qed.
Lemma lem1077325 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1077326 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term87 _24632 _24635 g) = (term92 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077325 _24635) (@lem1077324 _24632 _24635 g)). Qed.
Lemma lem1077327 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term86 _24632 _24635 g) = (term92 _24632 _24635 g).
Proof. exact (TRANS (@lem1077319 _24632 _24635 g) (@lem1077326 _24632 _24635 g)). Qed.
Lemma lem1077329 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1077330 {_24635 : Type'} (P : _24635 -> Prop) : (term93 _24635 P) = (term94 _24635 P).
Proof. exact (@lem18394 _24635 P). Qed.
Lemma lem1077331 {_24635 : Type'} (P : _24635 -> Prop) : (term95 _24635 P) = (term96 _24635 P).
Proof. exact (@lem1077330 _24635 (term33 _24635 P)). Qed.
Lemma lem1077332 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (term59 _24635 P x) = (P x).
Proof. exact (eq_refl (term59 _24635 P x)). Qed.
Lemma lem1077333 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1077335 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (term60 _24635 P x) = (term61 _24635 P x).
Proof. exact (MK_COMB (@lem1077333) (@lem1077332 _24635 P x)). Qed.
Lemma lem1077336 {_24635 : Type'} (P : _24635 -> Prop) : (term62 _24635 P) = (term63 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1077335 _24635 P x)). Qed.
Lemma lem1077337 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1077338 {_24635 : Type'} (P : _24635 -> Prop) : (term96 _24635 P) = (term94 _24635 P).
Proof. exact (MK_COMB (@lem1077337 _24635) (@lem1077336 _24635 P)). Qed.
Lemma lem1077339 {_24635 : Type'} (P : _24635 -> Prop) : (term95 _24635 P) = (term94 _24635 P).
Proof. exact (TRANS (@lem1077331 _24635 P) (@lem1077338 _24635 P)). Qed.
Lemma lem1077340 {_24635 : Type'} (P : _24635 -> Prop) : (term33 _24635 P) = (term33 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1077329 _24635 P x)). Qed.
Lemma lem1077341 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1077342 {_24635 : Type'} (P : _24635 -> Prop) : (term34 _24635 P) = (term34 _24635 P).
Proof. exact (MK_COMB (@lem1077341 _24635) (@lem1077340 _24635 P)). Qed.
Lemma lem1077344 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term30 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term30 _24632 _24635 P g x)). Qed.
Lemma lem1077345 {_24632 : Type'} (P : _24632 -> Prop) : (term93 _24632 P) = (term94 _24632 P).
Proof. exact (@lem18394 _24632 P). Qed.
Lemma lem1077346 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term97 _24632 _24635 P g) = (term98 _24632 _24635 P g).
Proof. exact (@lem1077345 _24632 (term31 _24632 _24635 P g)). Qed.
Lemma lem1077347 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term66 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term66 _24632 _24635 P g x)). Qed.
Lemma lem1077348 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1077350 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term67 _24632 _24635 P g x) = (term68 _24632 _24635 P g x).
Proof. exact (MK_COMB (@lem1077348) (@lem1077347 _24632 _24635 P g x)). Qed.
Lemma lem1077351 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term69 _24632 _24635 P g) = (term70 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077350 _24632 _24635 P g x)). Qed.
Lemma lem1077352 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1077353 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term98 _24632 _24635 P g) = (term99 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077352 _24632) (@lem1077351 _24632 _24635 P g)). Qed.
Lemma lem1077354 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term97 _24632 _24635 P g) = (term99 _24632 _24635 P g).
Proof. exact (TRANS (@lem1077346 _24632 _24635 P g) (@lem1077353 _24632 _24635 P g)). Qed.
Lemma lem1077355 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term31 _24632 _24635 P g) = (term31 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077344 _24632 _24635 P g x)). Qed.
Lemma lem1077356 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1077357 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term32 _24632 _24635 P g) = (term32 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077356 _24632) (@lem1077355 _24632 _24635 P g)). Qed.
Lemma lem1077358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1077359 {_24635 : Type'} (P : _24635 -> Prop) : (term100 _24635 P) = (term101 _24635 P).
Proof. exact (MK_COMB (@lem1077358) (@lem1077339 _24635 P)). Qed.
Lemma lem1077360 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term102 _24632 _24635 P g) = (term103 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077359 _24635 P) (@lem1077357 _24632 _24635 P g)). Qed.
Lemma lem1077361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1077362 {_24635 : Type'} (P : _24635 -> Prop) : (term104 _24635 P) = (term104 _24635 P).
Proof. exact (MK_COMB (@lem1077361) (@lem1077342 _24635 P)). Qed.
Lemma lem1077363 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term105 _24632 _24635 P g) = (term106 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077362 _24635 P) (@lem1077354 _24632 _24635 P g)). Qed.
Lemma lem1077364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077365 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term107 _24632 _24635 P g) = (term108 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077364) (@lem1077363 _24632 _24635 P g)). Qed.
Lemma lem1077366 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term109 _24632 _24635 P g) = (term110 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077365 _24632 _24635 P g) (@lem1077360 _24632 _24635 P g)). Qed.
Lemma lem1077367 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term111 _24632 _24635 P g) = (term109 _24632 _24635 P g).
Proof. exact (@lem17646 (term34 _24635 P) (term32 _24632 _24635 P g)). Qed.
Lemma lem1077368 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term111 _24632 _24635 P g) = (term110 _24632 _24635 P g).
Proof. exact (TRANS (@lem1077367 _24632 _24635 P g) (@lem1077366 _24632 _24635 P g)). Qed.
Lemma lem1077369 {_24635 : Type'} (P : type686 _24635) : (term84 _24635 P) = (term85 _24635 P).
Proof. exact (@lem18392 (_24635 -> Prop) P). Qed.
Lemma lem1077370 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term112 _24632 _24635 g) = (term113 _24632 _24635 g).
Proof. exact (@lem1077369 _24635 (term36 _24632 _24635 g)). Qed.
Lemma lem1077371 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term114 _24632 _24635 g P) = ((term34 _24635 P) = (term32 _24632 _24635 P g)).
Proof. exact (eq_refl (term114 _24632 _24635 g P)). Qed.
Lemma lem1077372 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1077373 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term115 _24632 _24635 g P) = (term111 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077372) (@lem1077371 _24632 _24635 P g)). Qed.
Lemma lem1077374 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term115 _24632 _24635 g P) = (term110 _24632 _24635 P g).
Proof. exact (TRANS (@lem1077373 _24632 _24635 P g) (@lem1077368 _24632 _24635 P g)). Qed.
Lemma lem1077375 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term116 _24632 _24635 g) = (term117 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077374 _24632 _24635 P g)). Qed.
Lemma lem1077376 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1077377 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term113 _24632 _24635 g) = (term118 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077376 _24635) (@lem1077375 _24632 _24635 g)). Qed.
Lemma lem1077378 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term112 _24632 _24635 g) = (term118 _24632 _24635 g).
Proof. exact (TRANS (@lem1077370 _24632 _24635 g) (@lem1077377 _24632 _24635 g)). Qed.
Lemma lem1077393 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term119 _24632 _24635 g f a b) = (term120 _24632 _24635 g f a b).
Proof. exact (@lem17646 (a = (g b)) ((f a) = b)). Qed.
Lemma lem1077394 {_24632 : Type'} (P : _24632 -> Prop) : (term55 _24632 P) = (term56 _24632 P).
Proof. exact (@lem18392 _24632 P). Qed.
Lemma lem1077395 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term121 _24632 _24635 g f a) = (term122 _24632 _24635 g f a).
Proof. exact (@lem1077394 _24632 (term26 _24632 _24635 g f a)). Qed.
Lemma lem1077396 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term123 _24632 _24635 g f a b) = ((a = (g b)) = ((f a) = b)).
Proof. exact (eq_refl (term123 _24632 _24635 g f a b)). Qed.
Lemma lem1077397 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1077398 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term124 _24632 _24635 g f a b) = (term119 _24632 _24635 g f a b).
Proof. exact (MK_COMB (@lem1077397) (@lem1077396 _24632 _24635 g f a b)). Qed.
Lemma lem1077399 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term124 _24632 _24635 g f a b) = (term120 _24632 _24635 g f a b).
Proof. exact (TRANS (@lem1077398 _24632 _24635 g f a b) (@lem1077393 _24632 _24635 g f a b)). Qed.
Lemma lem1077400 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term125 _24632 _24635 g f a) = (term126 _24632 _24635 g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1077399 _24632 _24635 g f a b)). Qed.
Lemma lem1077401 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1077402 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term122 _24632 _24635 g f a) = (term127 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077401 _24632) (@lem1077400 _24632 _24635 g f a)). Qed.
Lemma lem1077403 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term121 _24632 _24635 g f a) = (term127 _24632 _24635 g f a).
Proof. exact (TRANS (@lem1077395 _24632 _24635 g f a) (@lem1077402 _24632 _24635 g f a)). Qed.
Lemma lem1077404 {_24635 : Type'} (P : _24635 -> Prop) : (term55 _24635 P) = (term56 _24635 P).
Proof. exact (@lem18392 _24635 P). Qed.
Lemma lem1077405 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term128 _24632 _24635 g f) = (term129 _24632 _24635 g f).
Proof. exact (@lem1077404 _24635 (term28 _24632 _24635 g f)). Qed.
Lemma lem1077406 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term130 _24632 _24635 g f a) = (term27 _24632 _24635 g f a).
Proof. exact (eq_refl (term130 _24632 _24635 g f a)). Qed.
Lemma lem1077407 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1077408 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term131 _24632 _24635 g f a) = (term121 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077407) (@lem1077406 _24632 _24635 g f a)). Qed.
Lemma lem1077409 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term131 _24632 _24635 g f a) = (term127 _24632 _24635 g f a).
Proof. exact (TRANS (@lem1077408 _24632 _24635 g f a) (@lem1077403 _24632 _24635 g f a)). Qed.
Lemma lem1077410 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term132 _24632 _24635 g f) = (term133 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1077409 _24632 _24635 g f a)). Qed.
Lemma lem1077411 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1077412 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term129 _24632 _24635 g f) = (term134 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077411 _24635) (@lem1077410 _24632 _24635 g f)). Qed.
Lemma lem1077413 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term128 _24632 _24635 g f) = (term134 _24632 _24635 g f).
Proof. exact (TRANS (@lem1077405 _24632 _24635 g f) (@lem1077412 _24632 _24635 g f)). Qed.
Lemma lem1077414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077415 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term135 _24632 _24635 g) = (term136 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077414) (@lem1077378 _24632 _24635 g)). Qed.
Lemma lem1077416 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term137 _24632 _24635 g f) = (term138 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077415 _24632 _24635 g) (@lem1077413 _24632 _24635 g f)). Qed.
Lemma lem1077417 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term139 _24632 _24635 g f) = (term137 _24632 _24635 g f).
Proof. exact (@lem17045 (term37 _24632 _24635 g) (term29 _24632 _24635 g f)). Qed.
Lemma lem1077418 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term139 _24632 _24635 g f) = (term138 _24632 _24635 g f).
Proof. exact (TRANS (@lem1077417 _24632 _24635 g f) (@lem1077416 _24632 _24635 g f)). Qed.
Lemma lem1077419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077420 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term140 _24632 _24635 g) = (term141 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077419) (@lem1077327 _24632 _24635 g)). Qed.
Lemma lem1077421 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term142 _24632 _24635 g f) = (term143 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077420 _24632 _24635 g) (@lem1077418 _24632 _24635 g f)). Qed.
Lemma lem1077422 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term54 _24632 _24635 g f) = (term142 _24632 _24635 g f).
Proof. exact (@lem17045 (term44 _24632 _24635 g) (term39 _24632 _24635 g f)). Qed.
Lemma lem1077423 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term54 _24632 _24635 g f) = (term143 _24632 _24635 g f).
Proof. exact (TRANS (@lem1077422 _24632 _24635 g f) (@lem1077421 _24632 _24635 g f)). Qed.
Lemma lem1077425 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1077426 {_24635 : Type'} (P : type686 _24635) (Q : type686 _24635) : (term146 _24635 P Q) = (term147 _24635 P Q).
Proof. exact (@lem1077425 (_24635 -> Prop) P Q). Qed.
Lemma lem1077427 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term148 _24632 _24635 g) = (term149 _24632 _24635 g).
Proof. exact (@lem1077426 _24635 (term150 _24632 _24635 g) (term151 _24632 _24635 g)). Qed.
Lemma lem1077428 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term152 _24632 _24635 g P) = (term78 _24632 _24635 P g).
Proof. exact (eq_refl (term152 _24632 _24635 g P)). Qed.
Lemma lem1077429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077430 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term153 _24632 _24635 g P) = (term80 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077429) (@lem1077428 _24632 _24635 P g)). Qed.
Lemma lem1077431 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term154 _24632 _24635 g P) = (term75 _24632 _24635 P g).
Proof. exact (eq_refl (term154 _24632 _24635 g P)). Qed.
Lemma lem1077432 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term155 _24632 _24635 g P) = (term82 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077430 _24632 _24635 P g) (@lem1077431 _24632 _24635 P g)). Qed.
Lemma lem1077433 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term156 _24632 _24635 g) = (term91 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077432 _24632 _24635 P g)). Qed.
Lemma lem1077434 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1077435 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term148 _24632 _24635 g) = (term92 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077434 _24635) (@lem1077433 _24632 _24635 g)). Qed.
Lemma lem1077436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1077437 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term157 _24632 _24635 g) = (term158 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077436) (@lem1077435 _24632 _24635 g)). Qed.
Lemma lem1077438 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term152 _24632 _24635 g P) = (term78 _24632 _24635 P g).
Proof. exact (eq_refl (term152 _24632 _24635 g P)). Qed.
Lemma lem1077439 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term159 _24632 _24635 g) = (term150 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077438 _24632 _24635 P g)). Qed.
Lemma lem1077440 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1077441 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term160 _24632 _24635 g) = (term161 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077440 _24635) (@lem1077439 _24632 _24635 g)). Qed.
Lemma lem1077442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077443 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term162 _24632 _24635 g) = (term163 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077442) (@lem1077441 _24632 _24635 g)). Qed.
Lemma lem1077444 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term154 _24632 _24635 g P) = (term75 _24632 _24635 P g).
Proof. exact (eq_refl (term154 _24632 _24635 g P)). Qed.
Lemma lem1077445 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term164 _24632 _24635 g) = (term151 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077444 _24632 _24635 P g)). Qed.
Lemma lem1077446 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1077447 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term165 _24632 _24635 g) = (term166 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077446 _24635) (@lem1077445 _24632 _24635 g)). Qed.
Lemma lem1077448 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term149 _24632 _24635 g) = (term167 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077443 _24632 _24635 g) (@lem1077447 _24632 _24635 g)). Qed.
Lemma lem1077449 {_24632 _24635 : Type'} (g : _24632 -> _24635) : ((term148 _24632 _24635 g) = (term149 _24632 _24635 g)) = ((term92 _24632 _24635 g) = (term167 _24632 _24635 g)).
Proof. exact (MK_COMB (@lem1077437 _24632 _24635 g) (@lem1077448 _24632 _24635 g)). Qed.
Lemma lem1077450 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term92 _24632 _24635 g) = (term167 _24632 _24635 g).
Proof. exact (EQ_MP (@lem1077449 _24632 _24635 g) (@lem1077427 _24632 _24635 g)). Qed.
Lemma lem1077563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077564 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term141 _24632 _24635 g) = (term168 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077563) (@lem1077450 _24632 _24635 g)). Qed.
Lemma lem1077566 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1077567 {_24635 : Type'} (P : type686 _24635) (Q : type686 _24635) : (term146 _24635 P Q) = (term147 _24635 P Q).
Proof. exact (@lem1077566 (_24635 -> Prop) P Q). Qed.
Lemma lem1077568 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term169 _24632 _24635 g) = (term170 _24632 _24635 g).
Proof. exact (@lem1077567 _24635 (term171 _24632 _24635 g) (term172 _24632 _24635 g)). Qed.
Lemma lem1077569 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term173 _24632 _24635 g P) = (term106 _24632 _24635 P g).
Proof. exact (eq_refl (term173 _24632 _24635 g P)). Qed.
Lemma lem1077570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077571 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term174 _24632 _24635 g P) = (term108 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077570) (@lem1077569 _24632 _24635 P g)). Qed.
Lemma lem1077572 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term175 _24632 _24635 g P) = (term103 _24632 _24635 P g).
Proof. exact (eq_refl (term175 _24632 _24635 g P)). Qed.
Lemma lem1077573 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term176 _24632 _24635 g P) = (term110 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077571 _24632 _24635 P g) (@lem1077572 _24632 _24635 P g)). Qed.
Lemma lem1077574 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term177 _24632 _24635 g) = (term117 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077573 _24632 _24635 P g)). Qed.
Lemma lem1077575 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1077576 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term169 _24632 _24635 g) = (term118 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077575 _24635) (@lem1077574 _24632 _24635 g)). Qed.
Lemma lem1077577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1077578 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term178 _24632 _24635 g) = (term179 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077577) (@lem1077576 _24632 _24635 g)). Qed.
Lemma lem1077579 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term173 _24632 _24635 g P) = (term106 _24632 _24635 P g).
Proof. exact (eq_refl (term173 _24632 _24635 g P)). Qed.
Lemma lem1077580 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term180 _24632 _24635 g) = (term171 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077579 _24632 _24635 P g)). Qed.
Lemma lem1077581 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1077582 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term181 _24632 _24635 g) = (term182 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077581 _24635) (@lem1077580 _24632 _24635 g)). Qed.
Lemma lem1077583 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077584 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term183 _24632 _24635 g) = (term184 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077583) (@lem1077582 _24632 _24635 g)). Qed.
Lemma lem1077585 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term175 _24632 _24635 g P) = (term103 _24632 _24635 P g).
Proof. exact (eq_refl (term175 _24632 _24635 g P)). Qed.
Lemma lem1077586 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term185 _24632 _24635 g) = (term172 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077585 _24632 _24635 P g)). Qed.
Lemma lem1077587 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1077588 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term186 _24632 _24635 g) = (term187 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077587 _24635) (@lem1077586 _24632 _24635 g)). Qed.
Lemma lem1077589 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term170 _24632 _24635 g) = (term188 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077584 _24632 _24635 g) (@lem1077588 _24632 _24635 g)). Qed.
Lemma lem1077590 {_24632 _24635 : Type'} (g : _24632 -> _24635) : ((term169 _24632 _24635 g) = (term170 _24632 _24635 g)) = ((term118 _24632 _24635 g) = (term188 _24632 _24635 g)).
Proof. exact (MK_COMB (@lem1077578 _24632 _24635 g) (@lem1077589 _24632 _24635 g)). Qed.
Lemma lem1077591 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term118 _24632 _24635 g) = (term188 _24632 _24635 g).
Proof. exact (EQ_MP (@lem1077590 _24632 _24635 g) (@lem1077568 _24632 _24635 g)). Qed.
Lemma lem1077704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077705 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term136 _24632 _24635 g) = (term189 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077704) (@lem1077591 _24632 _24635 g)). Qed.
Lemma lem1077711 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1077712 {_24632 : Type'} (P : _24632 -> Prop) (Q : _24632 -> Prop) : (term144 _24632 P Q) = (term145 _24632 P Q).
Proof. exact (@lem1077711 _24632 P Q). Qed.
Lemma lem1077713 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term190 _24632 _24635 g f a) = (term191 _24632 _24635 g f a).
Proof. exact (@lem1077712 _24632 (term192 _24632 _24635 g f a) (term193 _24632 _24635 g f a)). Qed.
Lemma lem1077714 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term194 _24632 _24635 g f a b) = (term195 _24632 _24635 g f a b).
Proof. exact (eq_refl (term194 _24632 _24635 g f a b)). Qed.
Lemma lem1077715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077716 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term196 _24632 _24635 g f a b) = (term197 _24632 _24635 g f a b).
Proof. exact (MK_COMB (@lem1077715) (@lem1077714 _24632 _24635 g f a b)). Qed.
Lemma lem1077717 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term198 _24632 _24635 g f a b) = (term199 _24632 _24635 g f a b).
Proof. exact (eq_refl (term198 _24632 _24635 g f a b)). Qed.
Lemma lem1077718 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term200 _24632 _24635 g f a b) = (term120 _24632 _24635 g f a b).
Proof. exact (MK_COMB (@lem1077716 _24632 _24635 g f a b) (@lem1077717 _24632 _24635 g f a b)). Qed.
Lemma lem1077719 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term201 _24632 _24635 g f a) = (term126 _24632 _24635 g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1077718 _24632 _24635 g f a b)). Qed.
Lemma lem1077720 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1077721 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term190 _24632 _24635 g f a) = (term127 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077720 _24632) (@lem1077719 _24632 _24635 g f a)). Qed.
Lemma lem1077722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1077723 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term202 _24632 _24635 g f a) = (term203 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077722) (@lem1077721 _24632 _24635 g f a)). Qed.
Lemma lem1077724 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term194 _24632 _24635 g f a b) = (term195 _24632 _24635 g f a b).
Proof. exact (eq_refl (term194 _24632 _24635 g f a b)). Qed.
Lemma lem1077725 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term204 _24632 _24635 g f a) = (term192 _24632 _24635 g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1077724 _24632 _24635 g f a b)). Qed.
Lemma lem1077726 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1077727 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term205 _24632 _24635 g f a) = (term206 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077726 _24632) (@lem1077725 _24632 _24635 g f a)). Qed.
Lemma lem1077728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077729 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term207 _24632 _24635 g f a) = (term208 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077728) (@lem1077727 _24632 _24635 g f a)). Qed.
Lemma lem1077730 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term198 _24632 _24635 g f a b) = (term199 _24632 _24635 g f a b).
Proof. exact (eq_refl (term198 _24632 _24635 g f a b)). Qed.
Lemma lem1077731 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term209 _24632 _24635 g f a) = (term193 _24632 _24635 g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1077730 _24632 _24635 g f a b)). Qed.
Lemma lem1077732 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1077733 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term210 _24632 _24635 g f a) = (term211 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077732 _24632) (@lem1077731 _24632 _24635 g f a)). Qed.
Lemma lem1077734 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term191 _24632 _24635 g f a) = (term212 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077729 _24632 _24635 g f a) (@lem1077733 _24632 _24635 g f a)). Qed.
Lemma lem1077735 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term190 _24632 _24635 g f a) = (term191 _24632 _24635 g f a)) = ((term127 _24632 _24635 g f a) = (term212 _24632 _24635 g f a)).
Proof. exact (MK_COMB (@lem1077723 _24632 _24635 g f a) (@lem1077734 _24632 _24635 g f a)). Qed.
Lemma lem1077736 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term127 _24632 _24635 g f a) = (term212 _24632 _24635 g f a).
Proof. exact (EQ_MP (@lem1077735 _24632 _24635 g f a) (@lem1077713 _24632 _24635 g f a)). Qed.
Lemma lem1077833 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term133 _24632 _24635 g f) = (term213 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1077736 _24632 _24635 g f a)). Qed.
Lemma lem1077834 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1077835 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term134 _24632 _24635 g f) = (term214 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077834 _24635) (@lem1077833 _24632 _24635 g f)). Qed.
Lemma lem1077837 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1077838 {_24635 : Type'} (P : _24635 -> Prop) (Q : _24635 -> Prop) : (term144 _24635 P Q) = (term145 _24635 P Q).
Proof. exact (@lem1077837 _24635 P Q). Qed.
Lemma lem1077839 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term215 _24632 _24635 g f) = (term216 _24632 _24635 g f).
Proof. exact (@lem1077838 _24635 (term217 _24632 _24635 g f) (term218 _24632 _24635 g f)). Qed.
Lemma lem1077840 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term219 _24632 _24635 g f a) = (term206 _24632 _24635 g f a).
Proof. exact (eq_refl (term219 _24632 _24635 g f a)). Qed.
Lemma lem1077841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077842 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term220 _24632 _24635 g f a) = (term208 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077841) (@lem1077840 _24632 _24635 g f a)). Qed.
Lemma lem1077843 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term221 _24632 _24635 g f a) = (term211 _24632 _24635 g f a).
Proof. exact (eq_refl (term221 _24632 _24635 g f a)). Qed.
Lemma lem1077844 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term222 _24632 _24635 g f a) = (term212 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1077842 _24632 _24635 g f a) (@lem1077843 _24632 _24635 g f a)). Qed.
Lemma lem1077845 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term223 _24632 _24635 g f) = (term213 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1077844 _24632 _24635 g f a)). Qed.
Lemma lem1077846 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1077847 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term215 _24632 _24635 g f) = (term214 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077846 _24635) (@lem1077845 _24632 _24635 g f)). Qed.
Lemma lem1077848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1077849 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term224 _24632 _24635 g f) = (term225 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077848) (@lem1077847 _24632 _24635 g f)). Qed.
Lemma lem1077850 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term219 _24632 _24635 g f a) = (term206 _24632 _24635 g f a).
Proof. exact (eq_refl (term219 _24632 _24635 g f a)). Qed.
Lemma lem1077851 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term226 _24632 _24635 g f) = (term217 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1077850 _24632 _24635 g f a)). Qed.
Lemma lem1077852 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1077853 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term227 _24632 _24635 g f) = (term228 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077852 _24635) (@lem1077851 _24632 _24635 g f)). Qed.
Lemma lem1077854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077855 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term229 _24632 _24635 g f) = (term230 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077854) (@lem1077853 _24632 _24635 g f)). Qed.
Lemma lem1077856 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term221 _24632 _24635 g f a) = (term211 _24632 _24635 g f a).
Proof. exact (eq_refl (term221 _24632 _24635 g f a)). Qed.
Lemma lem1077857 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term231 _24632 _24635 g f) = (term218 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1077856 _24632 _24635 g f a)). Qed.
Lemma lem1077858 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1077859 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term232 _24632 _24635 g f) = (term233 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077858 _24635) (@lem1077857 _24632 _24635 g f)). Qed.
Lemma lem1077860 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term216 _24632 _24635 g f) = (term234 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077855 _24632 _24635 g f) (@lem1077859 _24632 _24635 g f)). Qed.
Lemma lem1077861 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term215 _24632 _24635 g f) = (term216 _24632 _24635 g f)) = ((term214 _24632 _24635 g f) = (term234 _24632 _24635 g f)).
Proof. exact (MK_COMB (@lem1077849 _24632 _24635 g f) (@lem1077860 _24632 _24635 g f)). Qed.
Lemma lem1077862 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term214 _24632 _24635 g f) = (term234 _24632 _24635 g f).
Proof. exact (EQ_MP (@lem1077861 _24632 _24635 g f) (@lem1077839 _24632 _24635 g f)). Qed.
Lemma lem1077967 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term134 _24632 _24635 g f) = (term234 _24632 _24635 g f).
Proof. exact (TRANS (@lem1077835 _24632 _24635 g f) (@lem1077862 _24632 _24635 g f)). Qed.
Lemma lem1077968 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term138 _24632 _24635 g f) = (term235 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077705 _24632 _24635 g) (@lem1077967 _24632 _24635 g f)). Qed.
Lemma lem1077969 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term143 _24632 _24635 g f) = (term236 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1077564 _24632 _24635 g) (@lem1077968 _24632 _24635 g f)). Qed.
Lemma lem1077971 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1077972 {_24632 : Type'} (P : Prop) (Q : _24632 -> Prop) : (term237 _24632 P Q) = (term238 _24632 P Q).
Proof. exact (@lem1077971 _24632 P Q). Qed.
Lemma lem1077973 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term239 _24632 _24635 P g) = (term240 _24632 _24635 P g).
Proof. exact (@lem1077972 _24632 (term41 _24635 P) (term70 _24632 _24635 P g)). Qed.
Lemma lem1077974 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term241 _24632 _24635 P g x) = (term68 _24632 _24635 P g x).
Proof. exact (eq_refl (term241 _24632 _24635 P g x)). Qed.
Lemma lem1077975 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term242 _24632 _24635 P g) = (term70 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077974 _24632 _24635 P g x)). Qed.
Lemma lem1077976 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1077977 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term243 _24632 _24635 P g) = (term71 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077976 _24632) (@lem1077975 _24632 _24635 P g)). Qed.
Lemma lem1077978 {_24635 : Type'} (P : _24635 -> Prop) : (term76 _24635 P) = (term76 _24635 P).
Proof. exact (eq_refl (term76 _24635 P)). Qed.
Lemma lem1077979 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term239 _24632 _24635 P g) = (term78 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077978 _24635 P) (@lem1077977 _24632 _24635 P g)). Qed.
Lemma lem1077980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1077981 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term244 _24632 _24635 P g) = (term245 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077980) (@lem1077979 _24632 _24635 P g)). Qed.
Lemma lem1077982 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term241 _24632 _24635 P g x) = (term68 _24632 _24635 P g x).
Proof. exact (eq_refl (term241 _24632 _24635 P g x)). Qed.
Lemma lem1077983 {_24635 : Type'} (P : _24635 -> Prop) : (term76 _24635 P) = (term76 _24635 P).
Proof. exact (eq_refl (term76 _24635 P)). Qed.
Lemma lem1077984 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term246 _24632 _24635 P g x) = (term247 _24632 _24635 P g x).
Proof. exact (MK_COMB (@lem1077983 _24635 P) (@lem1077982 _24632 _24635 P g x)). Qed.
Lemma lem1077985 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term248 _24632 _24635 P g) = (term249 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1077984 _24632 _24635 P g x)). Qed.
Lemma lem1077986 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1077987 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term240 _24632 _24635 P g) = (term250 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1077986 _24632) (@lem1077985 _24632 _24635 P g)). Qed.
Lemma lem1077988 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : ((term239 _24632 _24635 P g) = (term240 _24632 _24635 P g)) = ((term78 _24632 _24635 P g) = (term250 _24632 _24635 P g)).
Proof. exact (MK_COMB (@lem1077981 _24632 _24635 P g) (@lem1077987 _24632 _24635 P g)). Qed.
Lemma lem1077989 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term78 _24632 _24635 P g) = (term250 _24632 _24635 P g).
Proof. exact (EQ_MP (@lem1077988 _24632 _24635 P g) (@lem1077973 _24632 _24635 P g)). Qed.
Lemma lem1077990 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term150 _24632 _24635 g) = (term251 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1077989 _24632 _24635 P g)). Qed.
Lemma lem1077991 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1077992 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term161 _24632 _24635 g) = (term252 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077991 _24635) (@lem1077990 _24632 _24635 g)). Qed.
Lemma lem1077993 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1077994 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term163 _24632 _24635 g) = (term253 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077993) (@lem1077992 _24632 _24635 g)). Qed.
Lemma lem1077996 {A : Type'} (P : A -> Prop) (Q : Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1077997 {_24635 : Type'} (P : _24635 -> Prop) (Q : Prop) : (term254 _24635 P Q) = (term255 _24635 P Q).
Proof. exact (@lem1077996 _24635 P Q). Qed.
Lemma lem1077998 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term256 _24632 _24635 P g) = (term257 _24632 _24635 P g).
Proof. exact (@lem1077997 _24635 (term63 _24635 P) (term40 _24632 _24635 P g)). Qed.
Lemma lem1077999 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (term258 _24635 P x) = (term61 _24635 P x).
Proof. exact (eq_refl (term258 _24635 P x)). Qed.
Lemma lem1078000 {_24635 : Type'} (P : _24635 -> Prop) : (term259 _24635 P) = (term63 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1077999 _24635 P x)). Qed.
Lemma lem1078001 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078002 {_24635 : Type'} (P : _24635 -> Prop) : (term260 _24635 P) = (term56 _24635 P).
Proof. exact (MK_COMB (@lem1078001 _24635) (@lem1078000 _24635 P)). Qed.
Lemma lem1078003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1078004 {_24635 : Type'} (P : _24635 -> Prop) : (term261 _24635 P) = (term73 _24635 P).
Proof. exact (MK_COMB (@lem1078003) (@lem1078002 _24635 P)). Qed.
Lemma lem1078005 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term40 _24632 _24635 P g) = (term40 _24632 _24635 P g).
Proof. exact (eq_refl (term40 _24632 _24635 P g)). Qed.
Lemma lem1078006 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term256 _24632 _24635 P g) = (term75 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078004 _24635 P) (@lem1078005 _24632 _24635 P g)). Qed.
Lemma lem1078007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078008 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term262 _24632 _24635 P g) = (term263 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078007) (@lem1078006 _24632 _24635 P g)). Qed.
Lemma lem1078009 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (term258 _24635 P x) = (term61 _24635 P x).
Proof. exact (eq_refl (term258 _24635 P x)). Qed.
Lemma lem1078010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1078011 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (term264 _24635 P x) = (term265 _24635 P x).
Proof. exact (MK_COMB (@lem1078010) (@lem1078009 _24635 P x)). Qed.
Lemma lem1078012 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term40 _24632 _24635 P g) = (term40 _24632 _24635 P g).
Proof. exact (eq_refl (term40 _24632 _24635 P g)). Qed.
Lemma lem1078013 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term266 _24632 _24635 x P g) = (term267 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078011 _24635 P x) (@lem1078012 _24632 _24635 P g)). Qed.
Lemma lem1078014 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term268 _24632 _24635 P g) = (term269 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24635 => @lem1078013 _24632 _24635 x P g)). Qed.
Lemma lem1078015 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078016 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term257 _24632 _24635 P g) = (term270 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078015 _24635) (@lem1078014 _24632 _24635 P g)). Qed.
Lemma lem1078017 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : ((term256 _24632 _24635 P g) = (term257 _24632 _24635 P g)) = ((term75 _24632 _24635 P g) = (term270 _24632 _24635 P g)).
Proof. exact (MK_COMB (@lem1078008 _24632 _24635 P g) (@lem1078016 _24632 _24635 P g)). Qed.
Lemma lem1078018 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term75 _24632 _24635 P g) = (term270 _24632 _24635 P g).
Proof. exact (EQ_MP (@lem1078017 _24632 _24635 P g) (@lem1077998 _24632 _24635 P g)). Qed.
Lemma lem1078019 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term151 _24632 _24635 g) = (term271 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078018 _24632 _24635 P g)). Qed.
Lemma lem1078020 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078021 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term166 _24632 _24635 g) = (term272 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078020 _24635) (@lem1078019 _24632 _24635 g)). Qed.
Lemma lem1078022 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term167 _24632 _24635 g) = (term273 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1077994 _24632 _24635 g) (@lem1078021 _24632 _24635 g)). Qed.
Lemma lem1078024 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1078025 {_24635 : Type'} (P : type686 _24635) (Q : type686 _24635) : (term147 _24635 P Q) = (term146 _24635 P Q).
Proof. exact (@lem1078024 (_24635 -> Prop) P Q). Qed.
Lemma lem1078026 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term274 _24632 _24635 g) = (term275 _24632 _24635 g).
Proof. exact (@lem1078025 _24635 (term251 _24632 _24635 g) (term271 _24632 _24635 g)). Qed.
Lemma lem1078027 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term276 _24632 _24635 g P) = (term250 _24632 _24635 P g).
Proof. exact (eq_refl (term276 _24632 _24635 g P)). Qed.
Lemma lem1078028 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term277 _24632 _24635 g) = (term251 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078027 _24632 _24635 P g)). Qed.
Lemma lem1078029 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078030 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term278 _24632 _24635 g) = (term252 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078029 _24635) (@lem1078028 _24632 _24635 g)). Qed.
Lemma lem1078031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078032 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term279 _24632 _24635 g) = (term253 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078031) (@lem1078030 _24632 _24635 g)). Qed.
Lemma lem1078033 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term280 _24632 _24635 g P) = (term270 _24632 _24635 P g).
Proof. exact (eq_refl (term280 _24632 _24635 g P)). Qed.
Lemma lem1078034 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term281 _24632 _24635 g) = (term271 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078033 _24632 _24635 P g)). Qed.
Lemma lem1078035 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078036 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term282 _24632 _24635 g) = (term272 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078035 _24635) (@lem1078034 _24632 _24635 g)). Qed.
Lemma lem1078037 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term274 _24632 _24635 g) = (term273 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078032 _24632 _24635 g) (@lem1078036 _24632 _24635 g)). Qed.
Lemma lem1078038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078039 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term283 _24632 _24635 g) = (term284 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078038) (@lem1078037 _24632 _24635 g)). Qed.
Lemma lem1078040 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term276 _24632 _24635 g P) = (term250 _24632 _24635 P g).
Proof. exact (eq_refl (term276 _24632 _24635 g P)). Qed.
Lemma lem1078041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078042 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term285 _24632 _24635 g P) = (term286 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078041) (@lem1078040 _24632 _24635 P g)). Qed.
Lemma lem1078043 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term280 _24632 _24635 g P) = (term270 _24632 _24635 P g).
Proof. exact (eq_refl (term280 _24632 _24635 g P)). Qed.
Lemma lem1078044 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term287 _24632 _24635 g P) = (term288 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078042 _24632 _24635 P g) (@lem1078043 _24632 _24635 P g)). Qed.
Lemma lem1078045 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term289 _24632 _24635 g) = (term290 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078044 _24632 _24635 P g)). Qed.
Lemma lem1078046 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078047 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term275 _24632 _24635 g) = (term291 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078046 _24635) (@lem1078045 _24632 _24635 g)). Qed.
Lemma lem1078048 {_24632 _24635 : Type'} (g : _24632 -> _24635) : ((term274 _24632 _24635 g) = (term275 _24632 _24635 g)) = ((term273 _24632 _24635 g) = (term291 _24632 _24635 g)).
Proof. exact (MK_COMB (@lem1078039 _24632 _24635 g) (@lem1078047 _24632 _24635 g)). Qed.
Lemma lem1078049 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term273 _24632 _24635 g) = (term291 _24632 _24635 g).
Proof. exact (EQ_MP (@lem1078048 _24632 _24635 g) (@lem1078026 _24632 _24635 g)). Qed.
Lemma lem1078053 {A : Type'} (P : A -> Prop) (Q : Prop) : (term292 A P Q) = (term293 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1078054 {_24632 : Type'} (P : _24632 -> Prop) (Q : Prop) : (term292 _24632 P Q) = (term293 _24632 P Q).
Proof. exact (@lem1078053 _24632 P Q). Qed.
Lemma lem1078055 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term294 _24632 _24635 P g) = (term295 _24632 _24635 P g).
Proof. exact (@lem1078054 _24632 (term249 _24632 _24635 P g) (term270 _24632 _24635 P g)). Qed.
Lemma lem1078056 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term296 _24632 _24635 P g x) = (term247 _24632 _24635 P g x).
Proof. exact (eq_refl (term296 _24632 _24635 P g x)). Qed.
Lemma lem1078057 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term297 _24632 _24635 P g) = (term249 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078056 _24632 _24635 P g x)). Qed.
Lemma lem1078058 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078059 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term298 _24632 _24635 P g) = (term250 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078058 _24632) (@lem1078057 _24632 _24635 P g)). Qed.
Lemma lem1078060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078061 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term299 _24632 _24635 P g) = (term286 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078060) (@lem1078059 _24632 _24635 P g)). Qed.
Lemma lem1078062 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term270 _24632 _24635 P g) = (term270 _24632 _24635 P g).
Proof. exact (eq_refl (term270 _24632 _24635 P g)). Qed.
Lemma lem1078063 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term294 _24632 _24635 P g) = (term288 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078061 _24632 _24635 P g) (@lem1078062 _24632 _24635 P g)). Qed.
Lemma lem1078064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078065 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term300 _24632 _24635 P g) = (term301 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078064) (@lem1078063 _24632 _24635 P g)). Qed.
Lemma lem1078066 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term296 _24632 _24635 P g x) = (term247 _24632 _24635 P g x).
Proof. exact (eq_refl (term296 _24632 _24635 P g x)). Qed.
Lemma lem1078067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078068 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term302 _24632 _24635 P g x) = (term303 _24632 _24635 P g x).
Proof. exact (MK_COMB (@lem1078067) (@lem1078066 _24632 _24635 P g x)). Qed.
Lemma lem1078069 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term270 _24632 _24635 P g) = (term270 _24632 _24635 P g).
Proof. exact (eq_refl (term270 _24632 _24635 P g)). Qed.
Lemma lem1078070 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term304 _24632 _24635 x P g) = (term305 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078068 _24632 _24635 P g x) (@lem1078069 _24632 _24635 P g)). Qed.
Lemma lem1078071 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term306 _24632 _24635 P g) = (term307 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078070 _24632 _24635 x P g)). Qed.
Lemma lem1078072 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078073 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term295 _24632 _24635 P g) = (term308 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078072 _24632) (@lem1078071 _24632 _24635 P g)). Qed.
Lemma lem1078074 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : ((term294 _24632 _24635 P g) = (term295 _24632 _24635 P g)) = ((term288 _24632 _24635 P g) = (term308 _24632 _24635 P g)).
Proof. exact (MK_COMB (@lem1078065 _24632 _24635 P g) (@lem1078073 _24632 _24635 P g)). Qed.
Lemma lem1078075 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term288 _24632 _24635 P g) = (term308 _24632 _24635 P g).
Proof. exact (EQ_MP (@lem1078074 _24632 _24635 P g) (@lem1078055 _24632 _24635 P g)). Qed.
Lemma lem1078077 {A : Type'} (P : Prop) (Q : A -> Prop) : (term309 A P Q) = (term310 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1078078 {_24635 : Type'} (P : Prop) (Q : _24635 -> Prop) : (term309 _24635 P Q) = (term310 _24635 P Q).
Proof. exact (@lem1078077 _24635 P Q). Qed.
Lemma lem1078079 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term311 _24632 _24635 x P g) = (term312 _24632 _24635 x P g).
Proof. exact (@lem1078078 _24635 (term247 _24632 _24635 P g x) (term269 _24632 _24635 P g)). Qed.
Lemma lem1078080 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term313 _24632 _24635 P g x) = (term267 _24632 _24635 x P g).
Proof. exact (eq_refl (term313 _24632 _24635 P g x)). Qed.
Lemma lem1078081 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term314 _24632 _24635 P g) = (term269 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24635 => @lem1078080 _24632 _24635 x P g)). Qed.
Lemma lem1078082 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078083 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term315 _24632 _24635 P g) = (term270 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078082 _24635) (@lem1078081 _24632 _24635 P g)). Qed.
Lemma lem1078084 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term303 _24632 _24635 P g x) = (term303 _24632 _24635 P g x).
Proof. exact (eq_refl (term303 _24632 _24635 P g x)). Qed.
Lemma lem1078085 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term311 _24632 _24635 x P g) = (term305 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078084 _24632 _24635 P g x) (@lem1078083 _24632 _24635 P g)). Qed.
Lemma lem1078086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078087 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term316 _24632 _24635 x P g) = (term317 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078086) (@lem1078085 _24632 _24635 x P g)). Qed.
Lemma lem1078088 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term313 _24632 _24635 P g x) = (term267 _24632 _24635 x P g).
Proof. exact (eq_refl (term313 _24632 _24635 P g x)). Qed.
Lemma lem1078089 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term303 _24632 _24635 P g x) = (term303 _24632 _24635 P g x).
Proof. exact (eq_refl (term303 _24632 _24635 P g x)). Qed.
Lemma lem1078090 {_24632 _24635 : Type'} (x : _24632) (x' : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term318 _24632 _24635 x P g x') = (term319 _24632 _24635 x x' P g).
Proof. exact (MK_COMB (@lem1078089 _24632 _24635 P g x) (@lem1078088 _24632 _24635 x' P g)). Qed.
Lemma lem1078091 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term320 _24632 _24635 x P g) = (term321 _24632 _24635 x P g).
Proof. exact (fun_ext (fun x' : _24635 => @lem1078090 _24632 _24635 x x' P g)). Qed.
Lemma lem1078092 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078093 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term312 _24632 _24635 x P g) = (term322 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078092 _24635) (@lem1078091 _24632 _24635 x P g)). Qed.
Lemma lem1078094 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : ((term311 _24632 _24635 x P g) = (term312 _24632 _24635 x P g)) = ((term305 _24632 _24635 x P g) = (term322 _24632 _24635 x P g)).
Proof. exact (MK_COMB (@lem1078087 _24632 _24635 x P g) (@lem1078093 _24632 _24635 x P g)). Qed.
Lemma lem1078095 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term305 _24632 _24635 x P g) = (term322 _24632 _24635 x P g).
Proof. exact (EQ_MP (@lem1078094 _24632 _24635 x P g) (@lem1078079 _24632 _24635 x P g)). Qed.
Lemma lem1078096 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term307 _24632 _24635 P g) = (term323 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078095 _24632 _24635 x P g)). Qed.
Lemma lem1078097 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078098 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term308 _24632 _24635 P g) = (term324 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078097 _24632) (@lem1078096 _24632 _24635 P g)). Qed.
Lemma lem1078099 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term288 _24632 _24635 P g) = (term324 _24632 _24635 P g).
Proof. exact (TRANS (@lem1078075 _24632 _24635 P g) (@lem1078098 _24632 _24635 P g)). Qed.
Lemma lem1078100 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term290 _24632 _24635 g) = (term325 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078099 _24632 _24635 P g)). Qed.
Lemma lem1078101 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078102 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term291 _24632 _24635 g) = (term326 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078101 _24635) (@lem1078100 _24632 _24635 g)). Qed.
Lemma lem1078103 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term273 _24632 _24635 g) = (term326 _24632 _24635 g).
Proof. exact (TRANS (@lem1078049 _24632 _24635 g) (@lem1078102 _24632 _24635 g)). Qed.
Lemma lem1078104 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term167 _24632 _24635 g) = (term326 _24632 _24635 g).
Proof. exact (TRANS (@lem1078022 _24632 _24635 g) (@lem1078103 _24632 _24635 g)). Qed.
Lemma lem1078105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078106 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term168 _24632 _24635 g) = (term327 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078105) (@lem1078104 _24632 _24635 g)). Qed.
Lemma lem1078108 {A : Type'} (P : A -> Prop) (Q : Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1078109 {_24635 : Type'} (P : _24635 -> Prop) (Q : Prop) : (term254 _24635 P Q) = (term255 _24635 P Q).
Proof. exact (@lem1078108 _24635 P Q). Qed.
Lemma lem1078110 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term106 _24632 _24635 P g) = (term328 _24632 _24635 P g).
Proof. exact (@lem1078109 _24635 P (term99 _24632 _24635 P g)). Qed.
Lemma lem1078111 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term171 _24632 _24635 g) = (term329 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078110 _24632 _24635 P g)). Qed.
Lemma lem1078112 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078113 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term182 _24632 _24635 g) = (term330 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078112 _24635) (@lem1078111 _24632 _24635 g)). Qed.
Lemma lem1078114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078115 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term184 _24632 _24635 g) = (term331 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078114) (@lem1078113 _24632 _24635 g)). Qed.
Lemma lem1078117 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1078118 {_24632 : Type'} (P : Prop) (Q : _24632 -> Prop) : (term237 _24632 P Q) = (term238 _24632 P Q).
Proof. exact (@lem1078117 _24632 P Q). Qed.
Lemma lem1078119 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term332 _24632 _24635 P g) = (term333 _24632 _24635 P g).
Proof. exact (@lem1078118 _24632 (term94 _24635 P) (term31 _24632 _24635 P g)). Qed.
Lemma lem1078120 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term66 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term66 _24632 _24635 P g x)). Qed.
Lemma lem1078121 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term334 _24632 _24635 P g) = (term31 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078120 _24632 _24635 P g x)). Qed.
Lemma lem1078122 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078123 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term335 _24632 _24635 P g) = (term32 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078122 _24632) (@lem1078121 _24632 _24635 P g)). Qed.
Lemma lem1078124 {_24635 : Type'} (P : _24635 -> Prop) : (term101 _24635 P) = (term101 _24635 P).
Proof. exact (eq_refl (term101 _24635 P)). Qed.
Lemma lem1078125 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term332 _24632 _24635 P g) = (term103 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078124 _24635 P) (@lem1078123 _24632 _24635 P g)). Qed.
Lemma lem1078126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078127 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term336 _24632 _24635 P g) = (term337 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078126) (@lem1078125 _24632 _24635 P g)). Qed.
Lemma lem1078128 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term66 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term66 _24632 _24635 P g x)). Qed.
Lemma lem1078129 {_24635 : Type'} (P : _24635 -> Prop) : (term101 _24635 P) = (term101 _24635 P).
Proof. exact (eq_refl (term101 _24635 P)). Qed.
Lemma lem1078130 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term338 _24632 _24635 P g x) = (term339 _24632 _24635 P g x).
Proof. exact (MK_COMB (@lem1078129 _24635 P) (@lem1078128 _24632 _24635 P g x)). Qed.
Lemma lem1078131 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term340 _24632 _24635 P g) = (term341 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078130 _24632 _24635 P g x)). Qed.
Lemma lem1078132 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078133 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term333 _24632 _24635 P g) = (term342 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078132 _24632) (@lem1078131 _24632 _24635 P g)). Qed.
Lemma lem1078134 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : ((term332 _24632 _24635 P g) = (term333 _24632 _24635 P g)) = ((term103 _24632 _24635 P g) = (term342 _24632 _24635 P g)).
Proof. exact (MK_COMB (@lem1078127 _24632 _24635 P g) (@lem1078133 _24632 _24635 P g)). Qed.
Lemma lem1078135 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term103 _24632 _24635 P g) = (term342 _24632 _24635 P g).
Proof. exact (EQ_MP (@lem1078134 _24632 _24635 P g) (@lem1078119 _24632 _24635 P g)). Qed.
Lemma lem1078136 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term172 _24632 _24635 g) = (term343 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078135 _24632 _24635 P g)). Qed.
Lemma lem1078137 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078138 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term187 _24632 _24635 g) = (term344 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078137 _24635) (@lem1078136 _24632 _24635 g)). Qed.
Lemma lem1078139 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term188 _24632 _24635 g) = (term345 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078115 _24632 _24635 g) (@lem1078138 _24632 _24635 g)). Qed.
Lemma lem1078141 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1078142 {_24635 : Type'} (P : type686 _24635) (Q : type686 _24635) : (term147 _24635 P Q) = (term146 _24635 P Q).
Proof. exact (@lem1078141 (_24635 -> Prop) P Q). Qed.
Lemma lem1078143 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term346 _24632 _24635 g) = (term347 _24632 _24635 g).
Proof. exact (@lem1078142 _24635 (term329 _24632 _24635 g) (term343 _24632 _24635 g)). Qed.
Lemma lem1078144 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term348 _24632 _24635 g P) = (term328 _24632 _24635 P g).
Proof. exact (eq_refl (term348 _24632 _24635 g P)). Qed.
Lemma lem1078145 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term349 _24632 _24635 g) = (term329 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078144 _24632 _24635 P g)). Qed.
Lemma lem1078146 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078147 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term350 _24632 _24635 g) = (term330 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078146 _24635) (@lem1078145 _24632 _24635 g)). Qed.
Lemma lem1078148 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078149 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term351 _24632 _24635 g) = (term331 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078148) (@lem1078147 _24632 _24635 g)). Qed.
Lemma lem1078150 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term352 _24632 _24635 g P) = (term342 _24632 _24635 P g).
Proof. exact (eq_refl (term352 _24632 _24635 g P)). Qed.
Lemma lem1078151 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term353 _24632 _24635 g) = (term343 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078150 _24632 _24635 P g)). Qed.
Lemma lem1078152 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078153 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term354 _24632 _24635 g) = (term344 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078152 _24635) (@lem1078151 _24632 _24635 g)). Qed.
Lemma lem1078154 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term346 _24632 _24635 g) = (term345 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078149 _24632 _24635 g) (@lem1078153 _24632 _24635 g)). Qed.
Lemma lem1078155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078156 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term355 _24632 _24635 g) = (term356 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078155) (@lem1078154 _24632 _24635 g)). Qed.
Lemma lem1078157 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term348 _24632 _24635 g P) = (term328 _24632 _24635 P g).
Proof. exact (eq_refl (term348 _24632 _24635 g P)). Qed.
Lemma lem1078158 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078159 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term357 _24632 _24635 g P) = (term358 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078158) (@lem1078157 _24632 _24635 P g)). Qed.
Lemma lem1078160 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term352 _24632 _24635 g P) = (term342 _24632 _24635 P g).
Proof. exact (eq_refl (term352 _24632 _24635 g P)). Qed.
Lemma lem1078161 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term359 _24632 _24635 g P) = (term360 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078159 _24632 _24635 P g) (@lem1078160 _24632 _24635 P g)). Qed.
Lemma lem1078162 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term361 _24632 _24635 g) = (term362 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078161 _24632 _24635 P g)). Qed.
Lemma lem1078163 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078164 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term347 _24632 _24635 g) = (term363 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078163 _24635) (@lem1078162 _24632 _24635 g)). Qed.
Lemma lem1078165 {_24632 _24635 : Type'} (g : _24632 -> _24635) : ((term346 _24632 _24635 g) = (term347 _24632 _24635 g)) = ((term345 _24632 _24635 g) = (term363 _24632 _24635 g)).
Proof. exact (MK_COMB (@lem1078156 _24632 _24635 g) (@lem1078164 _24632 _24635 g)). Qed.
Lemma lem1078166 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term345 _24632 _24635 g) = (term363 _24632 _24635 g).
Proof. exact (EQ_MP (@lem1078165 _24632 _24635 g) (@lem1078143 _24632 _24635 g)). Qed.
Lemma lem1078170 {A : Type'} (P : A -> Prop) (Q : Prop) : (term292 A P Q) = (term293 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1078171 {_24635 : Type'} (P : _24635 -> Prop) (Q : Prop) : (term292 _24635 P Q) = (term293 _24635 P Q).
Proof. exact (@lem1078170 _24635 P Q). Qed.
Lemma lem1078172 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term364 _24632 _24635 P g) = (term365 _24632 _24635 P g).
Proof. exact (@lem1078171 _24635 (term366 _24632 _24635 P g) (term342 _24632 _24635 P g)). Qed.
Lemma lem1078173 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term367 _24632 _24635 P g x) = (term368 _24632 _24635 x P g).
Proof. exact (eq_refl (term367 _24632 _24635 P g x)). Qed.
Lemma lem1078174 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term369 _24632 _24635 P g) = (term366 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24635 => @lem1078173 _24632 _24635 x P g)). Qed.
Lemma lem1078175 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078176 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term370 _24632 _24635 P g) = (term328 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078175 _24635) (@lem1078174 _24632 _24635 P g)). Qed.
Lemma lem1078177 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078178 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term371 _24632 _24635 P g) = (term358 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078177) (@lem1078176 _24632 _24635 P g)). Qed.
Lemma lem1078179 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term342 _24632 _24635 P g) = (term342 _24632 _24635 P g).
Proof. exact (eq_refl (term342 _24632 _24635 P g)). Qed.
Lemma lem1078180 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term364 _24632 _24635 P g) = (term360 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078178 _24632 _24635 P g) (@lem1078179 _24632 _24635 P g)). Qed.
Lemma lem1078181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078182 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term372 _24632 _24635 P g) = (term373 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078181) (@lem1078180 _24632 _24635 P g)). Qed.
Lemma lem1078183 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term367 _24632 _24635 P g x) = (term368 _24632 _24635 x P g).
Proof. exact (eq_refl (term367 _24632 _24635 P g x)). Qed.
Lemma lem1078184 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078185 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term374 _24632 _24635 P g x) = (term375 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078184) (@lem1078183 _24632 _24635 x P g)). Qed.
Lemma lem1078186 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term342 _24632 _24635 P g) = (term342 _24632 _24635 P g).
Proof. exact (eq_refl (term342 _24632 _24635 P g)). Qed.
Lemma lem1078187 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term376 _24632 _24635 x P g) = (term377 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078185 _24632 _24635 x P g) (@lem1078186 _24632 _24635 P g)). Qed.
Lemma lem1078188 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term378 _24632 _24635 P g) = (term379 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24635 => @lem1078187 _24632 _24635 x P g)). Qed.
Lemma lem1078189 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078190 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term365 _24632 _24635 P g) = (term380 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078189 _24635) (@lem1078188 _24632 _24635 P g)). Qed.
Lemma lem1078191 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : ((term364 _24632 _24635 P g) = (term365 _24632 _24635 P g)) = ((term360 _24632 _24635 P g) = (term380 _24632 _24635 P g)).
Proof. exact (MK_COMB (@lem1078182 _24632 _24635 P g) (@lem1078190 _24632 _24635 P g)). Qed.
Lemma lem1078192 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term360 _24632 _24635 P g) = (term380 _24632 _24635 P g).
Proof. exact (EQ_MP (@lem1078191 _24632 _24635 P g) (@lem1078172 _24632 _24635 P g)). Qed.
Lemma lem1078194 {A : Type'} (P : Prop) (Q : A -> Prop) : (term309 A P Q) = (term310 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1078195 {_24632 : Type'} (P : Prop) (Q : _24632 -> Prop) : (term309 _24632 P Q) = (term310 _24632 P Q).
Proof. exact (@lem1078194 _24632 P Q). Qed.
Lemma lem1078196 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term381 _24632 _24635 x P g) = (term382 _24632 _24635 x P g).
Proof. exact (@lem1078195 _24632 (term368 _24632 _24635 x P g) (term341 _24632 _24635 P g)). Qed.
Lemma lem1078197 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term383 _24632 _24635 P g x) = (term339 _24632 _24635 P g x).
Proof. exact (eq_refl (term383 _24632 _24635 P g x)). Qed.
Lemma lem1078198 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term384 _24632 _24635 P g) = (term341 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078197 _24632 _24635 P g x)). Qed.
Lemma lem1078199 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078200 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term385 _24632 _24635 P g) = (term342 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078199 _24632) (@lem1078198 _24632 _24635 P g)). Qed.
Lemma lem1078201 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term375 _24632 _24635 x P g) = (term375 _24632 _24635 x P g).
Proof. exact (eq_refl (term375 _24632 _24635 x P g)). Qed.
Lemma lem1078202 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term381 _24632 _24635 x P g) = (term377 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078201 _24632 _24635 x P g) (@lem1078200 _24632 _24635 P g)). Qed.
Lemma lem1078203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078204 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term386 _24632 _24635 x P g) = (term387 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078203) (@lem1078202 _24632 _24635 x P g)). Qed.
Lemma lem1078205 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term383 _24632 _24635 P g x) = (term339 _24632 _24635 P g x).
Proof. exact (eq_refl (term383 _24632 _24635 P g x)). Qed.
Lemma lem1078206 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term375 _24632 _24635 x P g) = (term375 _24632 _24635 x P g).
Proof. exact (eq_refl (term375 _24632 _24635 x P g)). Qed.
Lemma lem1078207 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (x' : _24632) : (term388 _24632 _24635 x P g x') = (term389 _24632 _24635 x P g x').
Proof. exact (MK_COMB (@lem1078206 _24632 _24635 x P g) (@lem1078205 _24632 _24635 P g x')). Qed.
Lemma lem1078208 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term390 _24632 _24635 x P g) = (term391 _24632 _24635 x P g).
Proof. exact (fun_ext (fun x' : _24632 => @lem1078207 _24632 _24635 x P g x')). Qed.
Lemma lem1078209 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078210 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term382 _24632 _24635 x P g) = (term392 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078209 _24632) (@lem1078208 _24632 _24635 x P g)). Qed.
Lemma lem1078211 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : ((term381 _24632 _24635 x P g) = (term382 _24632 _24635 x P g)) = ((term377 _24632 _24635 x P g) = (term392 _24632 _24635 x P g)).
Proof. exact (MK_COMB (@lem1078204 _24632 _24635 x P g) (@lem1078210 _24632 _24635 x P g)). Qed.
Lemma lem1078212 {_24632 _24635 : Type'} (x : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term377 _24632 _24635 x P g) = (term392 _24632 _24635 x P g).
Proof. exact (EQ_MP (@lem1078211 _24632 _24635 x P g) (@lem1078196 _24632 _24635 x P g)). Qed.
Lemma lem1078213 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term379 _24632 _24635 P g) = (term393 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24635 => @lem1078212 _24632 _24635 x P g)). Qed.
Lemma lem1078214 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078215 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term380 _24632 _24635 P g) = (term394 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078214 _24635) (@lem1078213 _24632 _24635 P g)). Qed.
Lemma lem1078216 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term360 _24632 _24635 P g) = (term394 _24632 _24635 P g).
Proof. exact (TRANS (@lem1078192 _24632 _24635 P g) (@lem1078215 _24632 _24635 P g)). Qed.
Lemma lem1078217 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term362 _24632 _24635 g) = (term395 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078216 _24632 _24635 P g)). Qed.
Lemma lem1078218 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078219 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term363 _24632 _24635 g) = (term396 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078218 _24635) (@lem1078217 _24632 _24635 g)). Qed.
Lemma lem1078220 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term345 _24632 _24635 g) = (term396 _24632 _24635 g).
Proof. exact (TRANS (@lem1078166 _24632 _24635 g) (@lem1078219 _24632 _24635 g)). Qed.
Lemma lem1078221 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term188 _24632 _24635 g) = (term396 _24632 _24635 g).
Proof. exact (TRANS (@lem1078139 _24632 _24635 g) (@lem1078220 _24632 _24635 g)). Qed.
Lemma lem1078222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078223 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term189 _24632 _24635 g) = (term397 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078222) (@lem1078221 _24632 _24635 g)). Qed.
Lemma lem1078225 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1078226 {_24635 : Type'} (P : _24635 -> Prop) (Q : _24635 -> Prop) : (term145 _24635 P Q) = (term144 _24635 P Q).
Proof. exact (@lem1078225 _24635 P Q). Qed.
Lemma lem1078227 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term216 _24632 _24635 g f) = (term215 _24632 _24635 g f).
Proof. exact (@lem1078226 _24635 (term217 _24632 _24635 g f) (term218 _24632 _24635 g f)). Qed.
Lemma lem1078228 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term219 _24632 _24635 g f a) = (term206 _24632 _24635 g f a).
Proof. exact (eq_refl (term219 _24632 _24635 g f a)). Qed.
Lemma lem1078229 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term226 _24632 _24635 g f) = (term217 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078228 _24632 _24635 g f a)). Qed.
Lemma lem1078230 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078231 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term227 _24632 _24635 g f) = (term228 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078230 _24635) (@lem1078229 _24632 _24635 g f)). Qed.
Lemma lem1078232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078233 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term229 _24632 _24635 g f) = (term230 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078232) (@lem1078231 _24632 _24635 g f)). Qed.
Lemma lem1078234 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term221 _24632 _24635 g f a) = (term211 _24632 _24635 g f a).
Proof. exact (eq_refl (term221 _24632 _24635 g f a)). Qed.
Lemma lem1078235 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term231 _24632 _24635 g f) = (term218 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078234 _24632 _24635 g f a)). Qed.
Lemma lem1078236 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078237 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term232 _24632 _24635 g f) = (term233 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078236 _24635) (@lem1078235 _24632 _24635 g f)). Qed.
Lemma lem1078238 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term216 _24632 _24635 g f) = (term234 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078233 _24632 _24635 g f) (@lem1078237 _24632 _24635 g f)). Qed.
Lemma lem1078239 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078240 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term398 _24632 _24635 g f) = (term399 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078239) (@lem1078238 _24632 _24635 g f)). Qed.
Lemma lem1078241 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term219 _24632 _24635 g f a) = (term206 _24632 _24635 g f a).
Proof. exact (eq_refl (term219 _24632 _24635 g f a)). Qed.
Lemma lem1078242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078243 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term220 _24632 _24635 g f a) = (term208 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1078242) (@lem1078241 _24632 _24635 g f a)). Qed.
Lemma lem1078244 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term221 _24632 _24635 g f a) = (term211 _24632 _24635 g f a).
Proof. exact (eq_refl (term221 _24632 _24635 g f a)). Qed.
Lemma lem1078245 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term222 _24632 _24635 g f a) = (term212 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1078243 _24632 _24635 g f a) (@lem1078244 _24632 _24635 g f a)). Qed.
Lemma lem1078246 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term223 _24632 _24635 g f) = (term213 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078245 _24632 _24635 g f a)). Qed.
Lemma lem1078247 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078248 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term215 _24632 _24635 g f) = (term214 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078247 _24635) (@lem1078246 _24632 _24635 g f)). Qed.
Lemma lem1078249 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term216 _24632 _24635 g f) = (term215 _24632 _24635 g f)) = ((term234 _24632 _24635 g f) = (term214 _24632 _24635 g f)).
Proof. exact (MK_COMB (@lem1078240 _24632 _24635 g f) (@lem1078248 _24632 _24635 g f)). Qed.
Lemma lem1078250 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term234 _24632 _24635 g f) = (term214 _24632 _24635 g f).
Proof. exact (EQ_MP (@lem1078249 _24632 _24635 g f) (@lem1078227 _24632 _24635 g f)). Qed.
Lemma lem1078252 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1078253 {_24632 : Type'} (P : _24632 -> Prop) (Q : _24632 -> Prop) : (term145 _24632 P Q) = (term144 _24632 P Q).
Proof. exact (@lem1078252 _24632 P Q). Qed.
Lemma lem1078254 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term191 _24632 _24635 g f a) = (term190 _24632 _24635 g f a).
Proof. exact (@lem1078253 _24632 (term192 _24632 _24635 g f a) (term193 _24632 _24635 g f a)). Qed.
Lemma lem1078255 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term194 _24632 _24635 g f a b) = (term195 _24632 _24635 g f a b).
Proof. exact (eq_refl (term194 _24632 _24635 g f a b)). Qed.
Lemma lem1078256 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term204 _24632 _24635 g f a) = (term192 _24632 _24635 g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1078255 _24632 _24635 g f a b)). Qed.
Lemma lem1078257 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078258 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term205 _24632 _24635 g f a) = (term206 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1078257 _24632) (@lem1078256 _24632 _24635 g f a)). Qed.
Lemma lem1078259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078260 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term207 _24632 _24635 g f a) = (term208 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1078259) (@lem1078258 _24632 _24635 g f a)). Qed.
Lemma lem1078261 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term198 _24632 _24635 g f a b) = (term199 _24632 _24635 g f a b).
Proof. exact (eq_refl (term198 _24632 _24635 g f a b)). Qed.
Lemma lem1078262 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term209 _24632 _24635 g f a) = (term193 _24632 _24635 g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1078261 _24632 _24635 g f a b)). Qed.
Lemma lem1078263 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078264 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term210 _24632 _24635 g f a) = (term211 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1078263 _24632) (@lem1078262 _24632 _24635 g f a)). Qed.
Lemma lem1078265 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term191 _24632 _24635 g f a) = (term212 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1078260 _24632 _24635 g f a) (@lem1078264 _24632 _24635 g f a)). Qed.
Lemma lem1078266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078267 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term400 _24632 _24635 g f a) = (term401 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1078266) (@lem1078265 _24632 _24635 g f a)). Qed.
Lemma lem1078268 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term194 _24632 _24635 g f a b) = (term195 _24632 _24635 g f a b).
Proof. exact (eq_refl (term194 _24632 _24635 g f a b)). Qed.
Lemma lem1078269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078270 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term196 _24632 _24635 g f a b) = (term197 _24632 _24635 g f a b).
Proof. exact (MK_COMB (@lem1078269) (@lem1078268 _24632 _24635 g f a b)). Qed.
Lemma lem1078271 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term198 _24632 _24635 g f a b) = (term199 _24632 _24635 g f a b).
Proof. exact (eq_refl (term198 _24632 _24635 g f a b)). Qed.
Lemma lem1078272 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term200 _24632 _24635 g f a b) = (term120 _24632 _24635 g f a b).
Proof. exact (MK_COMB (@lem1078270 _24632 _24635 g f a b) (@lem1078271 _24632 _24635 g f a b)). Qed.
Lemma lem1078273 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term201 _24632 _24635 g f a) = (term126 _24632 _24635 g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1078272 _24632 _24635 g f a b)). Qed.
Lemma lem1078274 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078275 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term190 _24632 _24635 g f a) = (term127 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1078274 _24632) (@lem1078273 _24632 _24635 g f a)). Qed.
Lemma lem1078276 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term191 _24632 _24635 g f a) = (term190 _24632 _24635 g f a)) = ((term212 _24632 _24635 g f a) = (term127 _24632 _24635 g f a)).
Proof. exact (MK_COMB (@lem1078267 _24632 _24635 g f a) (@lem1078275 _24632 _24635 g f a)). Qed.
Lemma lem1078277 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term212 _24632 _24635 g f a) = (term127 _24632 _24635 g f a).
Proof. exact (EQ_MP (@lem1078276 _24632 _24635 g f a) (@lem1078254 _24632 _24635 g f a)). Qed.
Lemma lem1078278 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term213 _24632 _24635 g f) = (term133 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078277 _24632 _24635 g f a)). Qed.
Lemma lem1078279 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078280 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term214 _24632 _24635 g f) = (term134 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078279 _24635) (@lem1078278 _24632 _24635 g f)). Qed.
Lemma lem1078281 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term234 _24632 _24635 g f) = (term134 _24632 _24635 g f).
Proof. exact (TRANS (@lem1078250 _24632 _24635 g f) (@lem1078280 _24632 _24635 g f)). Qed.
Lemma lem1078282 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term235 _24632 _24635 g f) = (term402 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078223 _24632 _24635 g) (@lem1078281 _24632 _24635 g f)). Qed.
Lemma lem1078286 {A : Type'} (P : A -> Prop) (Q : Prop) : (term292 A P Q) = (term293 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1078287 {_24635 : Type'} (P : type686 _24635) (Q : Prop) : (term403 _24635 P Q) = (term404 _24635 P Q).
Proof. exact (@lem1078286 (_24635 -> Prop) P Q). Qed.
Lemma lem1078288 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term405 _24632 _24635 g f) = (term406 _24632 _24635 g f).
Proof. exact (@lem1078287 _24635 (term395 _24632 _24635 g) (term134 _24632 _24635 g f)). Qed.
Lemma lem1078289 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term407 _24632 _24635 g P) = (term394 _24632 _24635 P g).
Proof. exact (eq_refl (term407 _24632 _24635 g P)). Qed.
Lemma lem1078290 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term408 _24632 _24635 g) = (term395 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078289 _24632 _24635 P g)). Qed.
Lemma lem1078291 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078292 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term409 _24632 _24635 g) = (term396 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078291 _24635) (@lem1078290 _24632 _24635 g)). Qed.
Lemma lem1078293 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078294 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term410 _24632 _24635 g) = (term397 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078293) (@lem1078292 _24632 _24635 g)). Qed.
Lemma lem1078295 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term134 _24632 _24635 g f) = (term134 _24632 _24635 g f).
Proof. exact (eq_refl (term134 _24632 _24635 g f)). Qed.
Lemma lem1078296 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term405 _24632 _24635 g f) = (term402 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078294 _24632 _24635 g) (@lem1078295 _24632 _24635 g f)). Qed.
Lemma lem1078297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078298 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term411 _24632 _24635 g f) = (term412 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078297) (@lem1078296 _24632 _24635 g f)). Qed.
Lemma lem1078299 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term407 _24632 _24635 g P) = (term394 _24632 _24635 P g).
Proof. exact (eq_refl (term407 _24632 _24635 g P)). Qed.
Lemma lem1078300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078301 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term413 _24632 _24635 g P) = (term414 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078300) (@lem1078299 _24632 _24635 P g)). Qed.
Lemma lem1078302 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term134 _24632 _24635 g f) = (term134 _24632 _24635 g f).
Proof. exact (eq_refl (term134 _24632 _24635 g f)). Qed.
Lemma lem1078303 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term415 _24632 _24635 P g f) = (term416 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078301 _24632 _24635 P g) (@lem1078302 _24632 _24635 g f)). Qed.
Lemma lem1078304 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term417 _24632 _24635 g f) = (term418 _24632 _24635 g f).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078303 _24632 _24635 P g f)). Qed.
Lemma lem1078305 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078306 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term406 _24632 _24635 g f) = (term419 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078305 _24635) (@lem1078304 _24632 _24635 g f)). Qed.
Lemma lem1078307 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term405 _24632 _24635 g f) = (term406 _24632 _24635 g f)) = ((term402 _24632 _24635 g f) = (term419 _24632 _24635 g f)).
Proof. exact (MK_COMB (@lem1078298 _24632 _24635 g f) (@lem1078306 _24632 _24635 g f)). Qed.
Lemma lem1078308 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term402 _24632 _24635 g f) = (term419 _24632 _24635 g f).
Proof. exact (EQ_MP (@lem1078307 _24632 _24635 g f) (@lem1078288 _24632 _24635 g f)). Qed.
Lemma lem1078310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1078311 {_24635 : Type'} (P : _24635 -> Prop) (Q : _24635 -> Prop) : (term145 _24635 P Q) = (term144 _24635 P Q).
Proof. exact (@lem1078310 _24635 P Q). Qed.
Lemma lem1078312 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term420 _24632 _24635 P g f) = (term421 _24632 _24635 P g f).
Proof. exact (@lem1078311 _24635 (term393 _24632 _24635 P g) (term133 _24632 _24635 g f)). Qed.
Lemma lem1078313 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term422 _24632 _24635 P g a) = (term392 _24632 _24635 a P g).
Proof. exact (eq_refl (term422 _24632 _24635 P g a)). Qed.
Lemma lem1078314 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term423 _24632 _24635 P g) = (term393 _24632 _24635 P g).
Proof. exact (fun_ext (fun a : _24635 => @lem1078313 _24632 _24635 a P g)). Qed.
Lemma lem1078315 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078316 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term424 _24632 _24635 P g) = (term394 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078315 _24635) (@lem1078314 _24632 _24635 P g)). Qed.
Lemma lem1078317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078318 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term425 _24632 _24635 P g) = (term414 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078317) (@lem1078316 _24632 _24635 P g)). Qed.
Lemma lem1078319 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term426 _24632 _24635 g f a) = (term127 _24632 _24635 g f a).
Proof. exact (eq_refl (term426 _24632 _24635 g f a)). Qed.
Lemma lem1078320 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term427 _24632 _24635 g f) = (term133 _24632 _24635 g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078319 _24632 _24635 g f a)). Qed.
Lemma lem1078321 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078322 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term428 _24632 _24635 g f) = (term134 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078321 _24635) (@lem1078320 _24632 _24635 g f)). Qed.
Lemma lem1078323 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term420 _24632 _24635 P g f) = (term416 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078318 _24632 _24635 P g) (@lem1078322 _24632 _24635 g f)). Qed.
Lemma lem1078324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078325 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term429 _24632 _24635 P g f) = (term430 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078324) (@lem1078323 _24632 _24635 P g f)). Qed.
Lemma lem1078326 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term422 _24632 _24635 P g a) = (term392 _24632 _24635 a P g).
Proof. exact (eq_refl (term422 _24632 _24635 P g a)). Qed.
Lemma lem1078327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078328 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term431 _24632 _24635 P g a) = (term432 _24632 _24635 a P g).
Proof. exact (MK_COMB (@lem1078327) (@lem1078326 _24632 _24635 a P g)). Qed.
Lemma lem1078329 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term426 _24632 _24635 g f a) = (term127 _24632 _24635 g f a).
Proof. exact (eq_refl (term426 _24632 _24635 g f a)). Qed.
Lemma lem1078330 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term433 _24632 _24635 P g f a) = (term434 _24632 _24635 P g f a).
Proof. exact (MK_COMB (@lem1078328 _24632 _24635 a P g) (@lem1078329 _24632 _24635 g f a)). Qed.
Lemma lem1078331 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term435 _24632 _24635 P g f) = (term436 _24632 _24635 P g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078330 _24632 _24635 P g f a)). Qed.
Lemma lem1078332 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078333 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term421 _24632 _24635 P g f) = (term437 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078332 _24635) (@lem1078331 _24632 _24635 P g f)). Qed.
Lemma lem1078334 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term420 _24632 _24635 P g f) = (term421 _24632 _24635 P g f)) = ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f)).
Proof. exact (MK_COMB (@lem1078325 _24632 _24635 P g f) (@lem1078333 _24632 _24635 P g f)). Qed.
Lemma lem1078335 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f).
Proof. exact (EQ_MP (@lem1078334 _24632 _24635 P g f) (@lem1078312 _24632 _24635 P g f)). Qed.
Lemma lem1078338 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term438 _24632 _24635 P g f) = (term438 _24632 _24635 P g f).
Proof. exact (eq_refl (term438 _24632 _24635 P g f)). Qed.
Lemma lem1078339 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term438 _24632 _24635 P g f) = ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f)).
Proof. exact (eq_refl (term438 _24632 _24635 P g f)). Qed.
Lemma lem1078340 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term439 _24632 _24635 P g f) = (term439 _24632 _24635 P g f).
Proof. exact (eq_refl (term439 _24632 _24635 P g f)). Qed.
Lemma lem1078341 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term438 _24632 _24635 P g f) = (term438 _24632 _24635 P g f)) = ((term438 _24632 _24635 P g f) = ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f))).
Proof. exact (MK_COMB (@lem1078340 _24632 _24635 P g f) (@lem1078339 _24632 _24635 P g f)). Qed.
Lemma lem1078342 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term438 _24632 _24635 P g f) = ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f)).
Proof. exact (eq_refl (term438 _24632 _24635 P g f)). Qed.
Lemma lem1078343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078344 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term439 _24632 _24635 P g f) = (term440 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078343) (@lem1078342 _24632 _24635 P g f)). Qed.
Lemma lem1078345 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f)) = ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f)).
Proof. exact (eq_refl ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f))). Qed.
Lemma lem1078346 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term438 _24632 _24635 P g f) = ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f))) = (((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f)) = ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f))).
Proof. exact (MK_COMB (@lem1078344 _24632 _24635 P g f) (@lem1078345 _24632 _24635 P g f)). Qed.
Lemma lem1078347 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term438 _24632 _24635 P g f) = (term438 _24632 _24635 P g f)) = (((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f)) = ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f))).
Proof. exact (TRANS (@lem1078341 _24632 _24635 P g f) (@lem1078346 _24632 _24635 P g f)). Qed.
Lemma lem1078348 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f)) = ((term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f)).
Proof. exact (EQ_MP (@lem1078347 _24632 _24635 P g f) (@lem1078338 _24632 _24635 P g f)). Qed.
Lemma lem1078349 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term416 _24632 _24635 P g f) = (term437 _24632 _24635 P g f).
Proof. exact (EQ_MP (@lem1078348 _24632 _24635 P g f) (@lem1078335 _24632 _24635 P g f)). Qed.
Lemma lem1078351 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1078352 {_24632 : Type'} (P : _24632 -> Prop) (Q : _24632 -> Prop) : (term145 _24632 P Q) = (term144 _24632 P Q).
Proof. exact (@lem1078351 _24632 P Q). Qed.
Lemma lem1078353 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term441 _24632 _24635 P g f a) = (term442 _24632 _24635 P g f a).
Proof. exact (@lem1078352 _24632 (term391 _24632 _24635 a P g) (term126 _24632 _24635 g f a)). Qed.
Lemma lem1078354 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) : (term443 _24632 _24635 a P g b) = (term389 _24632 _24635 a P g b).
Proof. exact (eq_refl (term443 _24632 _24635 a P g b)). Qed.
Lemma lem1078355 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term444 _24632 _24635 a P g) = (term391 _24632 _24635 a P g).
Proof. exact (fun_ext (fun b : _24632 => @lem1078354 _24632 _24635 a P g b)). Qed.
Lemma lem1078356 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078357 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term445 _24632 _24635 a P g) = (term392 _24632 _24635 a P g).
Proof. exact (MK_COMB (@lem1078356 _24632) (@lem1078355 _24632 _24635 a P g)). Qed.
Lemma lem1078358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078359 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term446 _24632 _24635 a P g) = (term432 _24632 _24635 a P g).
Proof. exact (MK_COMB (@lem1078358) (@lem1078357 _24632 _24635 a P g)). Qed.
Lemma lem1078360 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term447 _24632 _24635 g f a b) = (term120 _24632 _24635 g f a b).
Proof. exact (eq_refl (term447 _24632 _24635 g f a b)). Qed.
Lemma lem1078361 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term448 _24632 _24635 g f a) = (term126 _24632 _24635 g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1078360 _24632 _24635 g f a b)). Qed.
Lemma lem1078362 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078363 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term449 _24632 _24635 g f a) = (term127 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1078362 _24632) (@lem1078361 _24632 _24635 g f a)). Qed.
Lemma lem1078364 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term441 _24632 _24635 P g f a) = (term434 _24632 _24635 P g f a).
Proof. exact (MK_COMB (@lem1078359 _24632 _24635 a P g) (@lem1078363 _24632 _24635 g f a)). Qed.
Lemma lem1078365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078366 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term450 _24632 _24635 P g f a) = (term451 _24632 _24635 P g f a).
Proof. exact (MK_COMB (@lem1078365) (@lem1078364 _24632 _24635 P g f a)). Qed.
Lemma lem1078367 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) : (term443 _24632 _24635 a P g b) = (term389 _24632 _24635 a P g b).
Proof. exact (eq_refl (term443 _24632 _24635 a P g b)). Qed.
Lemma lem1078368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078369 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) : (term452 _24632 _24635 a P g b) = (term453 _24632 _24635 a P g b).
Proof. exact (MK_COMB (@lem1078368) (@lem1078367 _24632 _24635 a P g b)). Qed.
Lemma lem1078370 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term447 _24632 _24635 g f a b) = (term120 _24632 _24635 g f a b).
Proof. exact (eq_refl (term447 _24632 _24635 g f a b)). Qed.
Lemma lem1078371 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term454 _24632 _24635 P g f a b) = (term455 _24632 _24635 P g f a b).
Proof. exact (MK_COMB (@lem1078369 _24632 _24635 a P g b) (@lem1078370 _24632 _24635 g f a b)). Qed.
Lemma lem1078372 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term456 _24632 _24635 P g f a) = (term457 _24632 _24635 P g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1078371 _24632 _24635 P g f a b)). Qed.
Lemma lem1078373 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078374 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term442 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a).
Proof. exact (MK_COMB (@lem1078373 _24632) (@lem1078372 _24632 _24635 P g f a)). Qed.
Lemma lem1078375 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term441 _24632 _24635 P g f a) = (term442 _24632 _24635 P g f a)) = ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a)).
Proof. exact (MK_COMB (@lem1078366 _24632 _24635 P g f a) (@lem1078374 _24632 _24635 P g f a)). Qed.
Lemma lem1078376 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a).
Proof. exact (EQ_MP (@lem1078375 _24632 _24635 P g f a) (@lem1078353 _24632 _24635 P g f a)). Qed.
Lemma lem1078379 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term459 _24632 _24635 P g f a) = (term459 _24632 _24635 P g f a).
Proof. exact (eq_refl (term459 _24632 _24635 P g f a)). Qed.
Lemma lem1078380 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term459 _24632 _24635 P g f a) = ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a)).
Proof. exact (eq_refl (term459 _24632 _24635 P g f a)). Qed.
Lemma lem1078381 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term460 _24632 _24635 P g f a) = (term460 _24632 _24635 P g f a).
Proof. exact (eq_refl (term460 _24632 _24635 P g f a)). Qed.
Lemma lem1078382 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term459 _24632 _24635 P g f a) = (term459 _24632 _24635 P g f a)) = ((term459 _24632 _24635 P g f a) = ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a))).
Proof. exact (MK_COMB (@lem1078381 _24632 _24635 P g f a) (@lem1078380 _24632 _24635 P g f a)). Qed.
Lemma lem1078383 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term459 _24632 _24635 P g f a) = ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a)).
Proof. exact (eq_refl (term459 _24632 _24635 P g f a)). Qed.
Lemma lem1078384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078385 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term460 _24632 _24635 P g f a) = (term461 _24632 _24635 P g f a).
Proof. exact (MK_COMB (@lem1078384) (@lem1078383 _24632 _24635 P g f a)). Qed.
Lemma lem1078386 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a)) = ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a)).
Proof. exact (eq_refl ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a))). Qed.
Lemma lem1078387 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term459 _24632 _24635 P g f a) = ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a))) = (((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a)) = ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a))).
Proof. exact (MK_COMB (@lem1078385 _24632 _24635 P g f a) (@lem1078386 _24632 _24635 P g f a)). Qed.
Lemma lem1078388 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term459 _24632 _24635 P g f a) = (term459 _24632 _24635 P g f a)) = (((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a)) = ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a))).
Proof. exact (TRANS (@lem1078382 _24632 _24635 P g f a) (@lem1078387 _24632 _24635 P g f a)). Qed.
Lemma lem1078389 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a)) = ((term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a)).
Proof. exact (EQ_MP (@lem1078388 _24632 _24635 P g f a) (@lem1078379 _24632 _24635 P g f a)). Qed.
Lemma lem1078390 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term434 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a).
Proof. exact (EQ_MP (@lem1078389 _24632 _24635 P g f a) (@lem1078376 _24632 _24635 P g f a)). Qed.
Lemma lem1078391 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term436 _24632 _24635 P g f) = (term462 _24632 _24635 P g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078390 _24632 _24635 P g f a)). Qed.
Lemma lem1078392 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078393 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term437 _24632 _24635 P g f) = (term463 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078392 _24635) (@lem1078391 _24632 _24635 P g f)). Qed.
Lemma lem1078394 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term416 _24632 _24635 P g f) = (term463 _24632 _24635 P g f).
Proof. exact (TRANS (@lem1078349 _24632 _24635 P g f) (@lem1078393 _24632 _24635 P g f)). Qed.
Lemma lem1078395 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term418 _24632 _24635 g f) = (term464 _24632 _24635 g f).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078394 _24632 _24635 P g f)). Qed.
Lemma lem1078396 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078397 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term419 _24632 _24635 g f) = (term465 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078396 _24635) (@lem1078395 _24632 _24635 g f)). Qed.
Lemma lem1078398 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term402 _24632 _24635 g f) = (term465 _24632 _24635 g f).
Proof. exact (TRANS (@lem1078308 _24632 _24635 g f) (@lem1078397 _24632 _24635 g f)). Qed.
Lemma lem1078399 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term235 _24632 _24635 g f) = (term465 _24632 _24635 g f).
Proof. exact (TRANS (@lem1078282 _24632 _24635 g f) (@lem1078398 _24632 _24635 g f)). Qed.
Lemma lem1078400 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term236 _24632 _24635 g f) = (term466 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078106 _24632 _24635 g) (@lem1078399 _24632 _24635 g f)). Qed.
Lemma lem1078402 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1078403 {_24635 : Type'} (P : type686 _24635) (Q : type686 _24635) : (term147 _24635 P Q) = (term146 _24635 P Q).
Proof. exact (@lem1078402 (_24635 -> Prop) P Q). Qed.
Lemma lem1078404 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term467 _24632 _24635 g f) = (term468 _24632 _24635 g f).
Proof. exact (@lem1078403 _24635 (term325 _24632 _24635 g) (term464 _24632 _24635 g f)). Qed.
Lemma lem1078405 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term469 _24632 _24635 g P) = (term324 _24632 _24635 P g).
Proof. exact (eq_refl (term469 _24632 _24635 g P)). Qed.
Lemma lem1078406 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term470 _24632 _24635 g) = (term325 _24632 _24635 g).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078405 _24632 _24635 P g)). Qed.
Lemma lem1078407 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078408 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term471 _24632 _24635 g) = (term326 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078407 _24635) (@lem1078406 _24632 _24635 g)). Qed.
Lemma lem1078409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078410 {_24632 _24635 : Type'} (g : _24632 -> _24635) : (term472 _24632 _24635 g) = (term327 _24632 _24635 g).
Proof. exact (MK_COMB (@lem1078409) (@lem1078408 _24632 _24635 g)). Qed.
Lemma lem1078411 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term473 _24632 _24635 g f P) = (term463 _24632 _24635 P g f).
Proof. exact (eq_refl (term473 _24632 _24635 g f P)). Qed.
Lemma lem1078412 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term474 _24632 _24635 g f) = (term464 _24632 _24635 g f).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078411 _24632 _24635 P g f)). Qed.
Lemma lem1078413 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078414 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term475 _24632 _24635 g f) = (term465 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078413 _24635) (@lem1078412 _24632 _24635 g f)). Qed.
Lemma lem1078415 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term467 _24632 _24635 g f) = (term466 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078410 _24632 _24635 g) (@lem1078414 _24632 _24635 g f)). Qed.
Lemma lem1078416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078417 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term476 _24632 _24635 g f) = (term477 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078416) (@lem1078415 _24632 _24635 g f)). Qed.
Lemma lem1078418 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term469 _24632 _24635 g P) = (term324 _24632 _24635 P g).
Proof. exact (eq_refl (term469 _24632 _24635 g P)). Qed.
Lemma lem1078419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078420 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term478 _24632 _24635 g P) = (term479 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078419) (@lem1078418 _24632 _24635 P g)). Qed.
Lemma lem1078421 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term473 _24632 _24635 g f P) = (term463 _24632 _24635 P g f).
Proof. exact (eq_refl (term473 _24632 _24635 g f P)). Qed.
Lemma lem1078422 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term480 _24632 _24635 g f P) = (term481 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078420 _24632 _24635 P g) (@lem1078421 _24632 _24635 P g f)). Qed.
Lemma lem1078423 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term482 _24632 _24635 g f) = (term483 _24632 _24635 g f).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078422 _24632 _24635 P g f)). Qed.
Lemma lem1078424 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078425 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term468 _24632 _24635 g f) = (term484 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078424 _24635) (@lem1078423 _24632 _24635 g f)). Qed.
Lemma lem1078426 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term467 _24632 _24635 g f) = (term468 _24632 _24635 g f)) = ((term466 _24632 _24635 g f) = (term484 _24632 _24635 g f)).
Proof. exact (MK_COMB (@lem1078417 _24632 _24635 g f) (@lem1078425 _24632 _24635 g f)). Qed.
Lemma lem1078427 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term466 _24632 _24635 g f) = (term484 _24632 _24635 g f).
Proof. exact (EQ_MP (@lem1078426 _24632 _24635 g f) (@lem1078404 _24632 _24635 g f)). Qed.
Lemma lem1078431 {A : Type'} (P : A -> Prop) (Q : Prop) : (term292 A P Q) = (term293 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1078432 {_24632 : Type'} (P : _24632 -> Prop) (Q : Prop) : (term292 _24632 P Q) = (term293 _24632 P Q).
Proof. exact (@lem1078431 _24632 P Q). Qed.
Lemma lem1078433 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term485 _24632 _24635 P g f) = (term486 _24632 _24635 P g f).
Proof. exact (@lem1078432 _24632 (term323 _24632 _24635 P g) (term463 _24632 _24635 P g f)). Qed.
Lemma lem1078434 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term487 _24632 _24635 P g x) = (term322 _24632 _24635 x P g).
Proof. exact (eq_refl (term487 _24632 _24635 P g x)). Qed.
Lemma lem1078435 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term488 _24632 _24635 P g) = (term323 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078434 _24632 _24635 x P g)). Qed.
Lemma lem1078436 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078437 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term489 _24632 _24635 P g) = (term324 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078436 _24632) (@lem1078435 _24632 _24635 P g)). Qed.
Lemma lem1078438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078439 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term490 _24632 _24635 P g) = (term479 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078438) (@lem1078437 _24632 _24635 P g)). Qed.
Lemma lem1078440 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term463 _24632 _24635 P g f) = (term463 _24632 _24635 P g f).
Proof. exact (eq_refl (term463 _24632 _24635 P g f)). Qed.
Lemma lem1078441 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term485 _24632 _24635 P g f) = (term481 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078439 _24632 _24635 P g) (@lem1078440 _24632 _24635 P g f)). Qed.
Lemma lem1078442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078443 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term491 _24632 _24635 P g f) = (term492 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078442) (@lem1078441 _24632 _24635 P g f)). Qed.
Lemma lem1078444 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term487 _24632 _24635 P g x) = (term322 _24632 _24635 x P g).
Proof. exact (eq_refl (term487 _24632 _24635 P g x)). Qed.
Lemma lem1078445 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078446 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term493 _24632 _24635 P g x) = (term494 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078445) (@lem1078444 _24632 _24635 x P g)). Qed.
Lemma lem1078447 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term463 _24632 _24635 P g f) = (term463 _24632 _24635 P g f).
Proof. exact (eq_refl (term463 _24632 _24635 P g f)). Qed.
Lemma lem1078448 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term495 _24632 _24635 x P g f) = (term496 _24632 _24635 x P g f).
Proof. exact (MK_COMB (@lem1078446 _24632 _24635 x P g) (@lem1078447 _24632 _24635 P g f)). Qed.
Lemma lem1078449 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term497 _24632 _24635 P g f) = (term498 _24632 _24635 P g f).
Proof. exact (fun_ext (fun x : _24632 => @lem1078448 _24632 _24635 x P g f)). Qed.
Lemma lem1078450 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078451 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term486 _24632 _24635 P g f) = (term499 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078450 _24632) (@lem1078449 _24632 _24635 P g f)). Qed.
Lemma lem1078452 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term485 _24632 _24635 P g f) = (term486 _24632 _24635 P g f)) = ((term481 _24632 _24635 P g f) = (term499 _24632 _24635 P g f)).
Proof. exact (MK_COMB (@lem1078443 _24632 _24635 P g f) (@lem1078451 _24632 _24635 P g f)). Qed.
Lemma lem1078453 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term481 _24632 _24635 P g f) = (term499 _24632 _24635 P g f).
Proof. exact (EQ_MP (@lem1078452 _24632 _24635 P g f) (@lem1078433 _24632 _24635 P g f)). Qed.
Lemma lem1078455 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1078456 {_24635 : Type'} (P : _24635 -> Prop) (Q : _24635 -> Prop) : (term145 _24635 P Q) = (term144 _24635 P Q).
Proof. exact (@lem1078455 _24635 P Q). Qed.
Lemma lem1078457 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term500 _24632 _24635 x P g f) = (term501 _24632 _24635 x P g f).
Proof. exact (@lem1078456 _24635 (term321 _24632 _24635 x P g) (term462 _24632 _24635 P g f)). Qed.
Lemma lem1078458 {_24632 _24635 : Type'} (x : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term502 _24632 _24635 x P g a) = (term319 _24632 _24635 x a P g).
Proof. exact (eq_refl (term502 _24632 _24635 x P g a)). Qed.
Lemma lem1078459 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term503 _24632 _24635 x P g) = (term321 _24632 _24635 x P g).
Proof. exact (fun_ext (fun a : _24635 => @lem1078458 _24632 _24635 x a P g)). Qed.
Lemma lem1078460 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078461 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term504 _24632 _24635 x P g) = (term322 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078460 _24635) (@lem1078459 _24632 _24635 x P g)). Qed.
Lemma lem1078462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078463 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term505 _24632 _24635 x P g) = (term494 _24632 _24635 x P g).
Proof. exact (MK_COMB (@lem1078462) (@lem1078461 _24632 _24635 x P g)). Qed.
Lemma lem1078464 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term506 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a).
Proof. exact (eq_refl (term506 _24632 _24635 P g f a)). Qed.
Lemma lem1078465 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term507 _24632 _24635 P g f) = (term462 _24632 _24635 P g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078464 _24632 _24635 P g f a)). Qed.
Lemma lem1078466 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078467 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term508 _24632 _24635 P g f) = (term463 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078466 _24635) (@lem1078465 _24632 _24635 P g f)). Qed.
Lemma lem1078468 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term500 _24632 _24635 x P g f) = (term496 _24632 _24635 x P g f).
Proof. exact (MK_COMB (@lem1078463 _24632 _24635 x P g) (@lem1078467 _24632 _24635 P g f)). Qed.
Lemma lem1078469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078470 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term509 _24632 _24635 x P g f) = (term510 _24632 _24635 x P g f).
Proof. exact (MK_COMB (@lem1078469) (@lem1078468 _24632 _24635 x P g f)). Qed.
Lemma lem1078471 {_24632 _24635 : Type'} (x : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term502 _24632 _24635 x P g a) = (term319 _24632 _24635 x a P g).
Proof. exact (eq_refl (term502 _24632 _24635 x P g a)). Qed.
Lemma lem1078472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078473 {_24632 _24635 : Type'} (x : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term511 _24632 _24635 x P g a) = (term512 _24632 _24635 x a P g).
Proof. exact (MK_COMB (@lem1078472) (@lem1078471 _24632 _24635 x a P g)). Qed.
Lemma lem1078474 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term506 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a).
Proof. exact (eq_refl (term506 _24632 _24635 P g f a)). Qed.
Lemma lem1078475 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term513 _24632 _24635 x P g f a) = (term514 _24632 _24635 x P g f a).
Proof. exact (MK_COMB (@lem1078473 _24632 _24635 x a P g) (@lem1078474 _24632 _24635 P g f a)). Qed.
Lemma lem1078476 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term515 _24632 _24635 x P g f) = (term516 _24632 _24635 x P g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078475 _24632 _24635 x P g f a)). Qed.
Lemma lem1078477 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078478 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term501 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f).
Proof. exact (MK_COMB (@lem1078477 _24635) (@lem1078476 _24632 _24635 x P g f)). Qed.
Lemma lem1078479 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term500 _24632 _24635 x P g f) = (term501 _24632 _24635 x P g f)) = ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f)).
Proof. exact (MK_COMB (@lem1078470 _24632 _24635 x P g f) (@lem1078478 _24632 _24635 x P g f)). Qed.
Lemma lem1078480 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f).
Proof. exact (EQ_MP (@lem1078479 _24632 _24635 x P g f) (@lem1078457 _24632 _24635 x P g f)). Qed.
Lemma lem1078483 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term518 _24632 _24635 x P g f) = (term518 _24632 _24635 x P g f).
Proof. exact (eq_refl (term518 _24632 _24635 x P g f)). Qed.
Lemma lem1078484 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term518 _24632 _24635 x P g f) = ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f)).
Proof. exact (eq_refl (term518 _24632 _24635 x P g f)). Qed.
Lemma lem1078485 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term519 _24632 _24635 x P g f) = (term519 _24632 _24635 x P g f).
Proof. exact (eq_refl (term519 _24632 _24635 x P g f)). Qed.
Lemma lem1078486 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term518 _24632 _24635 x P g f) = (term518 _24632 _24635 x P g f)) = ((term518 _24632 _24635 x P g f) = ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f))).
Proof. exact (MK_COMB (@lem1078485 _24632 _24635 x P g f) (@lem1078484 _24632 _24635 x P g f)). Qed.
Lemma lem1078487 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term518 _24632 _24635 x P g f) = ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f)).
Proof. exact (eq_refl (term518 _24632 _24635 x P g f)). Qed.
Lemma lem1078488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078489 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term519 _24632 _24635 x P g f) = (term520 _24632 _24635 x P g f).
Proof. exact (MK_COMB (@lem1078488) (@lem1078487 _24632 _24635 x P g f)). Qed.
Lemma lem1078490 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f)) = ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f)).
Proof. exact (eq_refl ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f))). Qed.
Lemma lem1078491 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term518 _24632 _24635 x P g f) = ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f))) = (((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f)) = ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f))).
Proof. exact (MK_COMB (@lem1078489 _24632 _24635 x P g f) (@lem1078490 _24632 _24635 x P g f)). Qed.
Lemma lem1078492 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term518 _24632 _24635 x P g f) = (term518 _24632 _24635 x P g f)) = (((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f)) = ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f))).
Proof. exact (TRANS (@lem1078486 _24632 _24635 x P g f) (@lem1078491 _24632 _24635 x P g f)). Qed.
Lemma lem1078493 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f)) = ((term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f)).
Proof. exact (EQ_MP (@lem1078492 _24632 _24635 x P g f) (@lem1078483 _24632 _24635 x P g f)). Qed.
Lemma lem1078494 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term496 _24632 _24635 x P g f) = (term517 _24632 _24635 x P g f).
Proof. exact (EQ_MP (@lem1078493 _24632 _24635 x P g f) (@lem1078480 _24632 _24635 x P g f)). Qed.
Lemma lem1078496 {A : Type'} (P : Prop) (Q : A -> Prop) : (term309 A P Q) = (term310 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1078497 {_24632 : Type'} (P : Prop) (Q : _24632 -> Prop) : (term309 _24632 P Q) = (term310 _24632 P Q).
Proof. exact (@lem1078496 _24632 P Q). Qed.
Lemma lem1078498 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term521 _24632 _24635 x P g f a) = (term522 _24632 _24635 x P g f a).
Proof. exact (@lem1078497 _24632 (term319 _24632 _24635 x a P g) (term457 _24632 _24635 P g f a)). Qed.
Lemma lem1078499 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term523 _24632 _24635 P g f a b) = (term455 _24632 _24635 P g f a b).
Proof. exact (eq_refl (term523 _24632 _24635 P g f a b)). Qed.
Lemma lem1078500 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term524 _24632 _24635 P g f a) = (term457 _24632 _24635 P g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1078499 _24632 _24635 P g f a b)). Qed.
Lemma lem1078501 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078502 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term525 _24632 _24635 P g f a) = (term458 _24632 _24635 P g f a).
Proof. exact (MK_COMB (@lem1078501 _24632) (@lem1078500 _24632 _24635 P g f a)). Qed.
Lemma lem1078503 {_24632 _24635 : Type'} (x : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term512 _24632 _24635 x a P g) = (term512 _24632 _24635 x a P g).
Proof. exact (eq_refl (term512 _24632 _24635 x a P g)). Qed.
Lemma lem1078504 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term521 _24632 _24635 x P g f a) = (term514 _24632 _24635 x P g f a).
Proof. exact (MK_COMB (@lem1078503 _24632 _24635 x a P g) (@lem1078502 _24632 _24635 P g f a)). Qed.
Lemma lem1078505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078506 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term526 _24632 _24635 x P g f a) = (term527 _24632 _24635 x P g f a).
Proof. exact (MK_COMB (@lem1078505) (@lem1078504 _24632 _24635 x P g f a)). Qed.
Lemma lem1078507 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term523 _24632 _24635 P g f a b) = (term455 _24632 _24635 P g f a b).
Proof. exact (eq_refl (term523 _24632 _24635 P g f a b)). Qed.
Lemma lem1078508 {_24632 _24635 : Type'} (x : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term512 _24632 _24635 x a P g) = (term512 _24632 _24635 x a P g).
Proof. exact (eq_refl (term512 _24632 _24635 x a P g)). Qed.
Lemma lem1078509 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term528 _24632 _24635 x P g f a b) = (term529 _24632 _24635 x P g f a b).
Proof. exact (MK_COMB (@lem1078508 _24632 _24635 x a P g) (@lem1078507 _24632 _24635 P g f a b)). Qed.
Lemma lem1078510 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term530 _24632 _24635 x P g f a) = (term531 _24632 _24635 x P g f a).
Proof. exact (fun_ext (fun b : _24632 => @lem1078509 _24632 _24635 x P g f a b)). Qed.
Lemma lem1078511 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078512 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term522 _24632 _24635 x P g f a) = (term532 _24632 _24635 x P g f a).
Proof. exact (MK_COMB (@lem1078511 _24632) (@lem1078510 _24632 _24635 x P g f a)). Qed.
Lemma lem1078513 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term521 _24632 _24635 x P g f a) = (term522 _24632 _24635 x P g f a)) = ((term514 _24632 _24635 x P g f a) = (term532 _24632 _24635 x P g f a)).
Proof. exact (MK_COMB (@lem1078506 _24632 _24635 x P g f a) (@lem1078512 _24632 _24635 x P g f a)). Qed.
Lemma lem1078514 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term514 _24632 _24635 x P g f a) = (term532 _24632 _24635 x P g f a).
Proof. exact (EQ_MP (@lem1078513 _24632 _24635 x P g f a) (@lem1078498 _24632 _24635 x P g f a)). Qed.
Lemma lem1078515 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term516 _24632 _24635 x P g f) = (term533 _24632 _24635 x P g f).
Proof. exact (fun_ext (fun a : _24635 => @lem1078514 _24632 _24635 x P g f a)). Qed.
Lemma lem1078516 {_24635 : Type'} : (@ex _24635) = (@ex _24635).
Proof. exact (eq_refl (@ex _24635)). Qed.
Lemma lem1078517 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term517 _24632 _24635 x P g f) = (term534 _24632 _24635 x P g f).
Proof. exact (MK_COMB (@lem1078516 _24635) (@lem1078515 _24632 _24635 x P g f)). Qed.
Lemma lem1078518 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term496 _24632 _24635 x P g f) = (term534 _24632 _24635 x P g f).
Proof. exact (TRANS (@lem1078494 _24632 _24635 x P g f) (@lem1078517 _24632 _24635 x P g f)). Qed.
Lemma lem1078519 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term498 _24632 _24635 P g f) = (term535 _24632 _24635 P g f).
Proof. exact (fun_ext (fun x : _24632 => @lem1078518 _24632 _24635 x P g f)). Qed.
Lemma lem1078520 {_24632 : Type'} : (@ex _24632) = (@ex _24632).
Proof. exact (eq_refl (@ex _24632)). Qed.
Lemma lem1078521 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term499 _24632 _24635 P g f) = (term536 _24632 _24635 P g f).
Proof. exact (MK_COMB (@lem1078520 _24632) (@lem1078519 _24632 _24635 P g f)). Qed.
Lemma lem1078522 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) : (term481 _24632 _24635 P g f) = (term536 _24632 _24635 P g f).
Proof. exact (TRANS (@lem1078453 _24632 _24635 P g f) (@lem1078521 _24632 _24635 P g f)). Qed.
Lemma lem1078523 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term483 _24632 _24635 g f) = (term537 _24632 _24635 g f).
Proof. exact (fun_ext (fun P : _24635 -> Prop => @lem1078522 _24632 _24635 P g f)). Qed.
Lemma lem1078524 {_24635 : Type'} : (@ex (_24635 -> Prop)) = (@ex (_24635 -> Prop)).
Proof. exact (eq_refl (@ex (_24635 -> Prop))). Qed.
Lemma lem1078525 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term484 _24632 _24635 g f) = (term538 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078524 _24635) (@lem1078523 _24632 _24635 g f)). Qed.
Lemma lem1078526 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term466 _24632 _24635 g f) = (term538 _24632 _24635 g f).
Proof. exact (TRANS (@lem1078427 _24632 _24635 g f) (@lem1078525 _24632 _24635 g f)). Qed.
Lemma lem1078527 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term236 _24632 _24635 g f) = (term538 _24632 _24635 g f).
Proof. exact (TRANS (@lem1078400 _24632 _24635 g f) (@lem1078526 _24632 _24635 g f)). Qed.
Lemma lem1078528 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term143 _24632 _24635 g f) = (term538 _24632 _24635 g f).
Proof. exact (TRANS (@lem1077969 _24632 _24635 g f) (@lem1078527 _24632 _24635 g f)). Qed.
Lemma lem1078529 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term54 _24632 _24635 g f) = (term538 _24632 _24635 g f).
Proof. exact (TRANS (@lem1077423 _24632 _24635 g f) (@lem1078528 _24632 _24635 g f)). Qed.
Lemma lem1078530 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term54 _24632 _24635 g f) : term538 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1078529 _24632 _24635 g f) (@lem1077252 _24632 _24635 g f h1)). Qed.
Lemma lem1078531 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term536 _24632 _24635 P g f) : term536 _24632 _24635 P g f.
Proof. exact (h1). Qed.
Lemma lem1078532 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term534 _24632 _24635 x P g f) : term534 _24632 _24635 x P g f.
Proof. exact (h1). Qed.
Lemma lem1078533 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (h1 : term532 _24632 _24635 x P g f a) : term532 _24632 _24635 x P g f a.
Proof. exact (h1). Qed.
Lemma lem1078534 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term529 _24632 _24635 x P g f a b) : term529 _24632 _24635 x P g f a b.
Proof. exact (h1). Qed.
Lemma lem1078543 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (y : _24635) : ((term46 _24632 _24635 g f y) = y) = ((term46 _24632 _24635 g f y) = y).
Proof. exact (eq_refl ((term46 _24632 _24635 g f y) = y)). Qed.
Lemma lem1078544 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term47 _24632 _24635 g f) = (term47 _24632 _24635 g f).
Proof. exact (fun_ext (fun y : _24635 => @lem1078543 _24632 _24635 g f y)). Qed.
Lemma lem1078545 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1078546 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term48 _24632 _24635 g f) = (term48 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078545 _24635) (@lem1078544 _24632 _24635 g f)). Qed.
Lemma lem1078555 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) (x : _24632) : ((term49 _24632 _24635 f g x) = x) = ((term49 _24632 _24635 f g x) = x).
Proof. exact (eq_refl ((term49 _24632 _24635 f g x) = x)). Qed.
Lemma lem1078556 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term50 _24632 _24635 f g) = (term50 _24632 _24635 f g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078555 _24632 _24635 f g x)). Qed.
Lemma lem1078557 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1078558 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term51 _24632 _24635 f g) = (term51 _24632 _24635 f g).
Proof. exact (MK_COMB (@lem1078557 _24632) (@lem1078556 _24632 _24635 f g)). Qed.
Lemma lem1078559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1078560 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term52 _24632 _24635 f g) = (term52 _24632 _24635 f g).
Proof. exact (MK_COMB (@lem1078559) (@lem1078558 _24632 _24635 f g)). Qed.
Lemma lem1078561 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term4 _24632 _24635 g f) = (term4 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078560 _24632 _24635 f g) (@lem1078546 _24632 _24635 g f)). Qed.
Lemma lem1078562 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term4 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1078561 _24632 _24635 g f) (@lem1077276 _24632 _24635 g f h1)). Qed.
Lemma lem1078603 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term120 _24632 _24635 g f a b) = (term120 _24632 _24635 g f a b).
Proof. exact (eq_refl (term120 _24632 _24635 g f a b)). Qed.
Lemma lem1078608 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) : (term30 _24632 _24635 P g b) = (term30 _24632 _24635 P g b).
Proof. exact (eq_refl (term30 _24632 _24635 P g b)). Qed.
Lemma lem1078613 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (term61 _24635 P x) = (term61 _24635 P x).
Proof. exact (eq_refl (term61 _24635 P x)). Qed.
Lemma lem1078614 {_24635 : Type'} (P : _24635 -> Prop) : (term63 _24635 P) = (term63 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1078613 _24635 P x)). Qed.
Lemma lem1078615 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1078616 {_24635 : Type'} (P : _24635 -> Prop) : (term94 _24635 P) = (term94 _24635 P).
Proof. exact (MK_COMB (@lem1078615 _24635) (@lem1078614 _24635 P)). Qed.
Lemma lem1078617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1078618 {_24635 : Type'} (P : _24635 -> Prop) : (term101 _24635 P) = (term101 _24635 P).
Proof. exact (MK_COMB (@lem1078617) (@lem1078616 _24635 P)). Qed.
Lemma lem1078619 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) : (term339 _24632 _24635 P g b) = (term339 _24632 _24635 P g b).
Proof. exact (MK_COMB (@lem1078618 _24635 P) (@lem1078608 _24632 _24635 P g b)). Qed.
Lemma lem1078626 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term68 _24632 _24635 P g x) = (term68 _24632 _24635 P g x).
Proof. exact (eq_refl (term68 _24632 _24635 P g x)). Qed.
Lemma lem1078627 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term70 _24632 _24635 P g) = (term70 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078626 _24632 _24635 P g x)). Qed.
Lemma lem1078628 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1078629 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term99 _24632 _24635 P g) = (term99 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078628 _24632) (@lem1078627 _24632 _24635 P g)). Qed.
Lemma lem1078634 {_24635 : Type'} (P : _24635 -> Prop) (a : _24635) : (term539 _24635 P a) = (term539 _24635 P a).
Proof. exact (eq_refl (term539 _24635 P a)). Qed.
Lemma lem1078635 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term368 _24632 _24635 a P g) = (term368 _24632 _24635 a P g).
Proof. exact (MK_COMB (@lem1078634 _24635 P a) (@lem1078629 _24632 _24635 P g)). Qed.
Lemma lem1078636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078637 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term375 _24632 _24635 a P g) = (term375 _24632 _24635 a P g).
Proof. exact (MK_COMB (@lem1078636) (@lem1078635 _24632 _24635 a P g)). Qed.
Lemma lem1078638 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) : (term389 _24632 _24635 a P g b) = (term389 _24632 _24635 a P g b).
Proof. exact (MK_COMB (@lem1078637 _24632 _24635 a P g) (@lem1078619 _24632 _24635 P g b)). Qed.
Lemma lem1078639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078640 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) : (term453 _24632 _24635 a P g b) = (term453 _24632 _24635 a P g b).
Proof. exact (MK_COMB (@lem1078639) (@lem1078638 _24632 _24635 a P g b)). Qed.
Lemma lem1078641 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term455 _24632 _24635 P g f a b) = (term455 _24632 _24635 P g f a b).
Proof. exact (MK_COMB (@lem1078640 _24632 _24635 a P g b) (@lem1078603 _24632 _24635 g f a b)). Qed.
Lemma lem1078646 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term30 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term30 _24632 _24635 P g x)). Qed.
Lemma lem1078647 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term31 _24632 _24635 P g) = (term31 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078646 _24632 _24635 P g x)). Qed.
Lemma lem1078648 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1078649 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term40 _24632 _24635 P g) = (term40 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078648 _24632) (@lem1078647 _24632 _24635 P g)). Qed.
Lemma lem1078656 {_24635 : Type'} (P : _24635 -> Prop) (a : _24635) : (term265 _24635 P a) = (term265 _24635 P a).
Proof. exact (eq_refl (term265 _24635 P a)). Qed.
Lemma lem1078657 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term267 _24632 _24635 a P g) = (term267 _24632 _24635 a P g).
Proof. exact (MK_COMB (@lem1078656 _24635 P a) (@lem1078649 _24632 _24635 P g)). Qed.
Lemma lem1078664 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term68 _24632 _24635 P g x) = (term68 _24632 _24635 P g x).
Proof. exact (eq_refl (term68 _24632 _24635 P g x)). Qed.
Lemma lem1078667 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1078668 {_24635 : Type'} (P : _24635 -> Prop) : (term33 _24635 P) = (term33 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1078667 _24635 P x)). Qed.
Lemma lem1078669 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1078670 {_24635 : Type'} (P : _24635 -> Prop) : (term41 _24635 P) = (term41 _24635 P).
Proof. exact (MK_COMB (@lem1078669 _24635) (@lem1078668 _24635 P)). Qed.
Lemma lem1078671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1078672 {_24635 : Type'} (P : _24635 -> Prop) : (term76 _24635 P) = (term76 _24635 P).
Proof. exact (MK_COMB (@lem1078671) (@lem1078670 _24635 P)). Qed.
Lemma lem1078673 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term247 _24632 _24635 P g x) = (term247 _24632 _24635 P g x).
Proof. exact (MK_COMB (@lem1078672 _24635 P) (@lem1078664 _24632 _24635 P g x)). Qed.
Lemma lem1078674 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078675 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term303 _24632 _24635 P g x) = (term303 _24632 _24635 P g x).
Proof. exact (MK_COMB (@lem1078674) (@lem1078673 _24632 _24635 P g x)). Qed.
Lemma lem1078676 {_24632 _24635 : Type'} (x : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term319 _24632 _24635 x a P g) = (term319 _24632 _24635 x a P g).
Proof. exact (MK_COMB (@lem1078675 _24632 _24635 P g x) (@lem1078657 _24632 _24635 a P g)). Qed.
Lemma lem1078677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1078678 {_24632 _24635 : Type'} (x : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) : (term512 _24632 _24635 x a P g) = (term512 _24632 _24635 x a P g).
Proof. exact (MK_COMB (@lem1078677) (@lem1078676 _24632 _24635 x a P g)). Qed.
Lemma lem1078679 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term529 _24632 _24635 x P g f a b) = (term529 _24632 _24635 x P g f a b).
Proof. exact (MK_COMB (@lem1078678 _24632 _24635 x a P g) (@lem1078641 _24632 _24635 P g f a b)). Qed.
Lemma lem1078680 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term529 _24632 _24635 x P g f a b) : term529 _24632 _24635 x P g f a b.
Proof. exact (EQ_MP (@lem1078679 _24632 _24635 x P g f a b) (@lem1078534 _24632 _24635 x P g f a b h1)). Qed.
Lemma lem1078681 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term48 _24632 _24635 g f.
Proof. exact (proj2 (@lem1078562 _24632 _24635 g f h1)). Qed.
Lemma lem1078682 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term51 _24632 _24635 f g.
Proof. exact (proj1 (@lem1078562 _24632 _24635 g f h1)). Qed.
Lemma lem1078683 {_24632 _24635 : Type'} (x : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term319 _24632 _24635 x a P g) : term319 _24632 _24635 x a P g.
Proof. exact (h1). Qed.
Lemma lem1078684 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term455 _24632 _24635 P g f a b) : term455 _24632 _24635 P g f a b.
Proof. exact (h1). Qed.
Lemma lem1078685 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term247 _24632 _24635 P g x.
Proof. exact (h1). Qed.
Lemma lem1078686 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term267 _24632 _24635 a P g.
Proof. exact (h1). Qed.
Lemma lem1078688 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term41 _24635 P.
Proof. exact (proj1 (@lem1078685 _24632 _24635 P g x h1)). Qed.
Lemma lem1078689 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term40 _24632 _24635 P g.
Proof. exact (proj2 (@lem1078686 _24632 _24635 a P g h1)). Qed.
Lemma lem1078691 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term389 _24632 _24635 a P g b) : term389 _24632 _24635 a P g b.
Proof. exact (h1). Qed.
Lemma lem1078692 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term120 _24632 _24635 g f a b) : term120 _24632 _24635 g f a b.
Proof. exact (h1). Qed.
Lemma lem1078693 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : term368 _24632 _24635 a P g.
Proof. exact (h1). Qed.
Lemma lem1078694 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term339 _24632 _24635 P g b.
Proof. exact (h1). Qed.
Lemma lem1078695 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : term99 _24632 _24635 P g.
Proof. exact (proj2 (@lem1078693 _24632 _24635 a P g h1)). Qed.
Lemma lem1078698 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term94 _24635 P.
Proof. exact (proj1 (@lem1078694 _24632 _24635 P g b h1)). Qed.
Lemma lem1078699 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term195 _24632 _24635 g f a b) : term195 _24632 _24635 g f a b.
Proof. exact (h1). Qed.
Lemma lem1078700 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term199 _24632 _24635 g f a b) : term199 _24632 _24635 g f a b.
Proof. exact (h1). Qed.
Lemma lem1078720 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1078721 {_24635 : Type'} (P : _24635 -> Prop) : (term33 _24635 P) = (term33 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1078720 _24635 P x)). Qed.
Lemma lem1078722 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1078724 {_24635 : Type'} (P : _24635 -> Prop) : (term41 _24635 P) = (term41 _24635 P).
Proof. exact (MK_COMB (@lem1078722 _24635) (@lem1078721 _24635 P)). Qed.
Lemma lem1078725 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term41 _24635 P.
Proof. exact (EQ_MP (@lem1078724 _24635 P) (@lem1078688 _24632 _24635 P g x h1)). Qed.
Lemma lem1078738 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (y : _24635) : ((term46 _24632 _24635 g f y) = y) = ((term46 _24632 _24635 g f y) = y).
Proof. exact (eq_refl ((term46 _24632 _24635 g f y) = y)). Qed.
Lemma lem1078739 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term47 _24632 _24635 g f) = (term47 _24632 _24635 g f).
Proof. exact (fun_ext (fun y : _24635 => @lem1078738 _24632 _24635 g f y)). Qed.
Lemma lem1078740 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1078742 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term48 _24632 _24635 g f) = (term48 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078740 _24635) (@lem1078739 _24632 _24635 g f)). Qed.
Lemma lem1078743 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term48 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1078742 _24632 _24635 g f) (@lem1078681 _24632 _24635 g f h1)). Qed.
Lemma lem1078749 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term30 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (eq_refl (term30 _24632 _24635 P g x)). Qed.
Lemma lem1078750 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term31 _24632 _24635 P g) = (term31 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078749 _24632 _24635 P g x)). Qed.
Lemma lem1078751 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1078753 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term40 _24632 _24635 P g) = (term40 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078751 _24632) (@lem1078750 _24632 _24635 P g)). Qed.
Lemma lem1078754 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term40 _24632 _24635 P g.
Proof. exact (EQ_MP (@lem1078753 _24632 _24635 P g) (@lem1078689 _24632 _24635 a P g h1)). Qed.
Lemma lem1078763 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (y : _24635) : ((term46 _24632 _24635 g f y) = y) = ((term46 _24632 _24635 g f y) = y).
Proof. exact (eq_refl ((term46 _24632 _24635 g f y) = y)). Qed.
Lemma lem1078764 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term47 _24632 _24635 g f) = (term47 _24632 _24635 g f).
Proof. exact (fun_ext (fun y : _24635 => @lem1078763 _24632 _24635 g f y)). Qed.
Lemma lem1078765 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1078767 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term48 _24632 _24635 g f) = (term48 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078765 _24635) (@lem1078764 _24632 _24635 g f)). Qed.
Lemma lem1078768 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term48 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1078767 _24632 _24635 g f) (@lem1078681 _24632 _24635 g f h1)). Qed.
Lemma lem1078774 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term68 _24632 _24635 P g x) = (term68 _24632 _24635 P g x).
Proof. exact (eq_refl (term68 _24632 _24635 P g x)). Qed.
Lemma lem1078775 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term70 _24632 _24635 P g) = (term70 _24632 _24635 P g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078774 _24632 _24635 P g x)). Qed.
Lemma lem1078776 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1078778 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) : (term99 _24632 _24635 P g) = (term99 _24632 _24635 P g).
Proof. exact (MK_COMB (@lem1078776 _24632) (@lem1078775 _24632 _24635 P g)). Qed.
Lemma lem1078779 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : term99 _24632 _24635 P g.
Proof. exact (EQ_MP (@lem1078778 _24632 _24635 P g) (@lem1078695 _24632 _24635 a P g h1)). Qed.
Lemma lem1078795 {_24635 : Type'} (P : _24635 -> Prop) (x : _24635) : (term61 _24635 P x) = (term61 _24635 P x).
Proof. exact (eq_refl (term61 _24635 P x)). Qed.
Lemma lem1078796 {_24635 : Type'} (P : _24635 -> Prop) : (term63 _24635 P) = (term63 _24635 P).
Proof. exact (fun_ext (fun x : _24635 => @lem1078795 _24635 P x)). Qed.
Lemma lem1078797 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1078799 {_24635 : Type'} (P : _24635 -> Prop) : (term94 _24635 P) = (term94 _24635 P).
Proof. exact (MK_COMB (@lem1078797 _24635) (@lem1078796 _24635 P)). Qed.
Lemma lem1078800 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term94 _24635 P.
Proof. exact (EQ_MP (@lem1078799 _24635 P) (@lem1078698 _24632 _24635 P g b h1)). Qed.
Lemma lem1078806 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) (x : _24632) : ((term49 _24632 _24635 f g x) = x) = ((term49 _24632 _24635 f g x) = x).
Proof. exact (eq_refl ((term49 _24632 _24635 f g x) = x)). Qed.
Lemma lem1078807 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term50 _24632 _24635 f g) = (term50 _24632 _24635 f g).
Proof. exact (fun_ext (fun x : _24632 => @lem1078806 _24632 _24635 f g x)). Qed.
Lemma lem1078808 {_24632 : Type'} : (@all _24632) = (@all _24632).
Proof. exact (eq_refl (@all _24632)). Qed.
Lemma lem1078810 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : (term51 _24632 _24635 f g) = (term51 _24632 _24635 f g).
Proof. exact (MK_COMB (@lem1078808 _24632) (@lem1078807 _24632 _24635 f g)). Qed.
Lemma lem1078811 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term51 _24632 _24635 f g.
Proof. exact (EQ_MP (@lem1078810 _24632 _24635 f g) (@lem1078682 _24632 _24635 g f h1)). Qed.
Lemma lem1078835 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (y : _24635) : ((term46 _24632 _24635 g f y) = y) = ((term46 _24632 _24635 g f y) = y).
Proof. exact (eq_refl ((term46 _24632 _24635 g f y) = y)). Qed.
Lemma lem1078836 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term47 _24632 _24635 g f) = (term47 _24632 _24635 g f).
Proof. exact (fun_ext (fun y : _24635 => @lem1078835 _24632 _24635 g f y)). Qed.
Lemma lem1078837 {_24635 : Type'} : (@all _24635) = (@all _24635).
Proof. exact (eq_refl (@all _24635)). Qed.
Lemma lem1078839 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term48 _24632 _24635 g f) = (term48 _24632 _24635 g f).
Proof. exact (MK_COMB (@lem1078837 _24635) (@lem1078836 _24632 _24635 g f)). Qed.
Lemma lem1078840 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term48 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1078839 _24632 _24635 g f) (@lem1078681 _24632 _24635 g f h1)). Qed.
Lemma lem1078855 {_24632 _24635 : Type'} (_17619 : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term59 _24635 P _17619.
Proof. exact (@lem1078725 _24632 _24635 P g x h1 _17619). Qed.
Lemma lem1078856 {_24635 : Type'} (P : _24635 -> Prop) (_17619 : _24635) : (term59 _24635 P _17619) = (P _17619).
Proof. exact (eq_refl (term59 _24635 P _17619)). Qed.
Lemma lem1078861 {_24632 _24635 : Type'} (_17621 : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term540 _24632 _24635 g f _17621.
Proof. exact (@lem1078743 _24632 _24635 g f h1 _17621). Qed.
Lemma lem1078862 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (_17621 : _24635) : (term540 _24632 _24635 g f _17621) = ((term46 _24632 _24635 g f _17621) = _17621).
Proof. exact (eq_refl (term540 _24632 _24635 g f _17621)). Qed.
Lemma lem1078864 {_24632 _24635 : Type'} (_17622 : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term66 _24632 _24635 P g _17622.
Proof. exact (@lem1078754 _24632 _24635 a P g h1 _17622). Qed.
Lemma lem1078865 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (_17622 : _24632) : (term66 _24632 _24635 P g _17622) = (term30 _24632 _24635 P g _17622).
Proof. exact (eq_refl (term66 _24632 _24635 P g _17622)). Qed.
Lemma lem1078870 {_24632 _24635 : Type'} (_17624 : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term540 _24632 _24635 g f _17624.
Proof. exact (@lem1078768 _24632 _24635 g f h1 _17624). Qed.
Lemma lem1078871 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (_17624 : _24635) : (term540 _24632 _24635 g f _17624) = ((term46 _24632 _24635 g f _17624) = _17624).
Proof. exact (eq_refl (term540 _24632 _24635 g f _17624)). Qed.
Lemma lem1078873 {_24632 _24635 : Type'} (_17625 : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : term241 _24632 _24635 P g _17625.
Proof. exact (@lem1078779 _24632 _24635 a P g h1 _17625). Qed.
Lemma lem1078874 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (_17625 : _24632) : (term241 _24632 _24635 P g _17625) = (term68 _24632 _24635 P g _17625).
Proof. exact (eq_refl (term241 _24632 _24635 P g _17625)). Qed.
Lemma lem1078882 {_24632 _24635 : Type'} (_17628 : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term258 _24635 P _17628.
Proof. exact (@lem1078800 _24632 _24635 P g b h1 _17628). Qed.
Lemma lem1078883 {_24635 : Type'} (P : _24635 -> Prop) (_17628 : _24635) : (term258 _24635 P _17628) = (term61 _24635 P _17628).
Proof. exact (eq_refl (term258 _24635 P _17628)). Qed.
Lemma lem1078885 {_24632 _24635 : Type'} (_17629 : _24632) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term541 _24632 _24635 f g _17629.
Proof. exact (@lem1078811 _24632 _24635 g f h1 _17629). Qed.
Lemma lem1078886 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) (_17629 : _24632) : (term541 _24632 _24635 f g _17629) = ((term49 _24632 _24635 f g _17629) = _17629).
Proof. exact (eq_refl (term541 _24632 _24635 f g _17629)). Qed.
Lemma lem1078894 {_24632 _24635 : Type'} (_17632 : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term540 _24632 _24635 g f _17632.
Proof. exact (@lem1078840 _24632 _24635 g f h1 _17632). Qed.
Lemma lem1078895 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (_17632 : _24635) : (term540 _24632 _24635 g f _17632) = ((term46 _24632 _24635 g f _17632) = _17632).
Proof. exact (eq_refl (term540 _24632 _24635 g f _17632)). Qed.
Lemma lem1078904 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term68 _24632 _24635 P g x.
Proof. exact (proj2 (@lem1078685 _24632 _24635 P g x h1)). Qed.
Lemma lem1078910 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term61 _24635 P a.
Proof. exact (proj1 (@lem1078686 _24632 _24635 a P g h1)). Qed.
Lemma lem1078920 {_24632 _24635 : Type'} (_17625 : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : term68 _24632 _24635 P g _17625.
Proof. exact (EQ_MP (@lem1078874 _24632 _24635 P g _17625) (@lem1078873 _24632 _24635 _17625 a P g h1)). Qed.
Lemma lem1078926 {_24632 _24635 : Type'} (_17628 : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term61 _24635 P _17628.
Proof. exact (EQ_MP (@lem1078883 _24635 P _17628) (@lem1078882 _24632 _24635 _17628 P g b h1)). Qed.
Lemma lem1078934 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term195 _24632 _24635 g f a b) : a = (g b).
Proof. exact (proj1 (@lem1078699 _24632 _24635 g f a b h1)). Qed.
Lemma lem1078936 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term195 _24632 _24635 g f a b) : term542 _24632 _24635 f a b.
Proof. exact (proj2 (@lem1078699 _24632 _24635 g f a b h1)). Qed.
Lemma lem1078942 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term199 _24632 _24635 g f a b) : term543 _24632 _24635 a g b.
Proof. exact (proj1 (@lem1078700 _24632 _24635 g f a b h1)). Qed.
Lemma lem1078944 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term199 _24632 _24635 g f a b) : (f a) = b.
Proof. exact (proj2 (@lem1078700 _24632 _24635 g f a b h1)). Qed.
Lemma lem1078987 {_24632 _24635 : Type'} (f : _24635 -> _24632) (b : _24632) : (term544 _24632 _24635 f b) = (term544 _24632 _24635 f b).
Proof. exact (eq_refl (term544 _24632 _24635 f b)). Qed.
Lemma lem1078988 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term195 _24632 _24635 g f a b) : (term545 _24632 _24635 f b a) = (term546 _24632 _24635 f g b).
Proof. exact (MK_COMB (@lem1078987 _24632 _24635 f b) (@lem1078934 _24632 _24635 g f a b h1)). Qed.
Lemma lem1078989 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) (b : _24632) : (term546 _24632 _24635 f g b) = (term547 _24632 _24635 f g b).
Proof. exact (eq_refl (term546 _24632 _24635 f g b)). Qed.
Lemma lem1078990 {_24632 _24635 : Type'} (f : _24635 -> _24632) (b : _24632) (a : _24635) : (term548 _24632 _24635 f b a) = (term548 _24632 _24635 f b a).
Proof. exact (eq_refl (term548 _24632 _24635 f b a)). Qed.
Lemma lem1078991 {_24632 _24635 : Type'} (a : _24635) (f : _24635 -> _24632) (g : _24632 -> _24635) (b : _24632) : ((term545 _24632 _24635 f b a) = (term546 _24632 _24635 f g b)) = ((term545 _24632 _24635 f b a) = (term547 _24632 _24635 f g b)).
Proof. exact (MK_COMB (@lem1078990 _24632 _24635 f b a) (@lem1078989 _24632 _24635 f g b)). Qed.
Lemma lem1078992 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term545 _24632 _24635 f b a) = (term542 _24632 _24635 f a b).
Proof. exact (eq_refl (term545 _24632 _24635 f b a)). Qed.
Lemma lem1078993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1078994 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (b : _24632) : (term548 _24632 _24635 f b a) = (term549 _24632 _24635 f a b).
Proof. exact (MK_COMB (@lem1078993) (@lem1078992 _24632 _24635 f a b)). Qed.
Lemma lem1078995 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) (b : _24632) : (term547 _24632 _24635 f g b) = (term547 _24632 _24635 f g b).
Proof. exact (eq_refl (term547 _24632 _24635 f g b)). Qed.
Lemma lem1078996 {_24632 _24635 : Type'} (a : _24635) (f : _24635 -> _24632) (g : _24632 -> _24635) (b : _24632) : ((term545 _24632 _24635 f b a) = (term547 _24632 _24635 f g b)) = ((term542 _24632 _24635 f a b) = (term547 _24632 _24635 f g b)).
Proof. exact (MK_COMB (@lem1078994 _24632 _24635 f a b) (@lem1078995 _24632 _24635 f g b)). Qed.
Lemma lem1078997 {_24632 _24635 : Type'} (a : _24635) (f : _24635 -> _24632) (g : _24632 -> _24635) (b : _24632) : ((term545 _24632 _24635 f b a) = (term546 _24632 _24635 f g b)) = ((term542 _24632 _24635 f a b) = (term547 _24632 _24635 f g b)).
Proof. exact (TRANS (@lem1078991 _24632 _24635 a f g b) (@lem1078996 _24632 _24635 a f g b)). Qed.
Lemma lem1078998 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term195 _24632 _24635 g f a b) : (term542 _24632 _24635 f a b) = (term547 _24632 _24635 f g b).
Proof. exact (EQ_MP (@lem1078997 _24632 _24635 a f g b) (@lem1078988 _24632 _24635 g f a b h1)). Qed.
Lemma lem1078999 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term195 _24632 _24635 g f a b) : term547 _24632 _24635 f g b.
Proof. exact (EQ_MP (@lem1078998 _24632 _24635 g f a b h1) (@lem1078936 _24632 _24635 g f a b h1)). Qed.
Lemma lem1079000 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term199 _24632 _24635 g f a b) : b = (f a).
Proof. exact (SYM (@lem1078944 _24632 _24635 g f a b h1)). Qed.
Lemma lem1079043 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) : (term550 _24632 _24635 a g) = (term550 _24632 _24635 a g).
Proof. exact (eq_refl (term550 _24632 _24635 a g)). Qed.
Lemma lem1079044 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term199 _24632 _24635 g f a b) : (term551 _24632 _24635 a g b) = (term552 _24632 _24635 g f a).
Proof. exact (MK_COMB (@lem1079043 _24632 _24635 a g) (@lem1079000 _24632 _24635 g f a b h1)). Qed.
Lemma lem1079045 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term552 _24632 _24635 g f a) = (term553 _24632 _24635 g f a).
Proof. exact (eq_refl (term552 _24632 _24635 g f a)). Qed.
Lemma lem1079046 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (b : _24632) : (term554 _24632 _24635 a g b) = (term554 _24632 _24635 a g b).
Proof. exact (eq_refl (term554 _24632 _24635 a g b)). Qed.
Lemma lem1079047 {_24632 _24635 : Type'} (b : _24632) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term551 _24632 _24635 a g b) = (term552 _24632 _24635 g f a)) = ((term551 _24632 _24635 a g b) = (term553 _24632 _24635 g f a)).
Proof. exact (MK_COMB (@lem1079046 _24632 _24635 a g b) (@lem1079045 _24632 _24635 g f a)). Qed.
Lemma lem1079048 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (b : _24632) : (term551 _24632 _24635 a g b) = (term543 _24632 _24635 a g b).
Proof. exact (eq_refl (term551 _24632 _24635 a g b)). Qed.
Lemma lem1079049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1079050 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (b : _24632) : (term554 _24632 _24635 a g b) = (term555 _24632 _24635 a g b).
Proof. exact (MK_COMB (@lem1079049) (@lem1079048 _24632 _24635 a g b)). Qed.
Lemma lem1079051 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term553 _24632 _24635 g f a) = (term553 _24632 _24635 g f a).
Proof. exact (eq_refl (term553 _24632 _24635 g f a)). Qed.
Lemma lem1079052 {_24632 _24635 : Type'} (b : _24632) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term551 _24632 _24635 a g b) = (term553 _24632 _24635 g f a)) = ((term543 _24632 _24635 a g b) = (term553 _24632 _24635 g f a)).
Proof. exact (MK_COMB (@lem1079050 _24632 _24635 a g b) (@lem1079051 _24632 _24635 g f a)). Qed.
Lemma lem1079053 {_24632 _24635 : Type'} (b : _24632) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : ((term551 _24632 _24635 a g b) = (term552 _24632 _24635 g f a)) = ((term543 _24632 _24635 a g b) = (term553 _24632 _24635 g f a)).
Proof. exact (TRANS (@lem1079047 _24632 _24635 b g f a) (@lem1079052 _24632 _24635 b g f a)). Qed.
Lemma lem1079054 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term199 _24632 _24635 g f a b) : (term543 _24632 _24635 a g b) = (term553 _24632 _24635 g f a).
Proof. exact (EQ_MP (@lem1079053 _24632 _24635 b g f a) (@lem1079044 _24632 _24635 g f a b h1)). Qed.
Lemma lem1079055 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term199 _24632 _24635 g f a b) : term553 _24632 _24635 g f a.
Proof. exact (EQ_MP (@lem1079054 _24632 _24635 g f a b h1) (@lem1078942 _24632 _24635 g f a b h1)). Qed.
Lemma lem1079089 {_24632 _24635 : Type'} (_17619 : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : P _17619.
Proof. exact (EQ_MP (@lem1078856 _24635 P _17619) (@lem1078855 _24632 _24635 _17619 P g x h1)). Qed.
Lemma lem1079090 {_24632 _24635 : Type'} (_17619 : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : P _17619.
Proof. exact (@lem1079089 _24632 _24635 _17619 P g x h1). Qed.
Lemma lem1079091 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term30 _24632 _24635 P g x.
Proof. exact (@lem1079090 _24632 _24635 (g x) P g x h1). Qed.
Lemma lem1079092 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term556 _24632 _24635 P g x.
Proof. exact (fun h0 : term68 _24632 _24635 P g x => @lem1079091 _24632 _24635 P g x h1). Qed.
Lemma lem1079094 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079095 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term556 _24632 _24635 P g x) = (term30 _24632 _24635 P g x).
Proof. exact (@lem1079094 (term30 _24632 _24635 P g x)). Qed.
Lemma lem1079096 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term30 _24632 _24635 P g x.
Proof. exact (EQ_MP (@lem1079095 _24632 _24635 P g x) (@lem1079092 _24632 _24635 P g x h1)). Qed.
Lemma lem1079099 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1079101 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) : (term68 _24632 _24635 P g x) = (term558 _24632 _24635 P g x).
Proof. exact (@lem1079099 (term30 _24632 _24635 P g x)). Qed.
Lemma lem1079104 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term558 _24632 _24635 P g x.
Proof. exact (EQ_MP (@lem1079101 _24632 _24635 P g x) (@lem1078904 _24632 _24635 P g x h1)). Qed.
Lemma lem1079107 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : False.
Proof. exact (@lem1079104 _24632 _24635 P g x h1 (@lem1079096 _24632 _24635 P g x h1)). Qed.
Lemma lem1079108 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : term559.
Proof. exact (fun h0 : ~ False => @lem1079107 _24632 _24635 P g x h1). Qed.
Lemma lem1079110 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079111 : term559 = False.
Proof. exact (@lem1079110 False). Qed.
Lemma lem1079112 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (x : _24632) (h1 : term247 _24632 _24635 P g x) : False.
Proof. exact (EQ_MP (@lem1079111) (@lem1079108 _24632 _24635 P g x h1)). Qed.
Lemma lem1079113 {_24635 : Type'} (P : _24635 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1079114 {_24635 : Type'} (_17655 : _24635) (_17656 : _24635) (h1 : _17655 = _17656) : _17655 = _17656.
Proof. exact (h1). Qed.
Lemma lem1079115 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) (h1 : _17655 = _17656) : (P _17655) = (P _17656).
Proof. exact (MK_COMB (@lem1079113 _24635 P) (@lem1079114 _24635 _17655 _17656 h1)). Qed.
Lemma lem1079117 (b : Prop) (a : Prop) : term560 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1079118 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : term561 _24635 _17656 P _17655.
Proof. exact (@lem1079117 (P _17656) (P _17655)). Qed.
Lemma lem1079119 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) (h1 : _17655 = _17656) : term562 _24635 _17656 P _17655.
Proof. exact (@lem1079118 _24635 _17656 P _17655 (@lem1079115 _24635 P _17655 _17656 h1)). Qed.
Lemma lem1079120 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : term563 _24635 _17656 P _17655.
Proof. exact (fun h0 : _17655 = _17656 => @lem1079119 _24635 P _17655 _17656 h0). Qed.
Lemma lem1079122 (a : Prop) (b : Prop) : (a -> b) = (term564 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1079123 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : (term563 _24635 _17656 P _17655) = (term565 _24635 _17656 P _17655).
Proof. exact (@lem1079122 (_17655 = _17656) (term562 _24635 _17656 P _17655)). Qed.
Lemma lem1079124 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : term565 _24635 _17656 P _17655.
Proof. exact (EQ_MP (@lem1079123 _24635 _17656 P _17655) (@lem1079120 _24635 _17656 P _17655)). Qed.
Lemma lem1079146 {_24632 _24635 : Type'} (_17621 : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f _17621) = _17621.
Proof. exact (EQ_MP (@lem1078862 _24632 _24635 g f _17621) (@lem1078861 _24632 _24635 _17621 g f h1)). Qed.
Lemma lem1079147 {_24632 _24635 : Type'} (_17621 : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f _17621) = _17621.
Proof. exact (@lem1079146 _24632 _24635 _17621 g f h1). Qed.
Lemma lem1079148 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f a) = a.
Proof. exact (@lem1079147 _24632 _24635 a g f h1). Qed.
Lemma lem1079149 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term566 _24632 _24635 g f a.
Proof. exact (fun h0 : term567 _24632 _24635 g f a => @lem1079148 _24632 _24635 a g f h1). Qed.
Lemma lem1079151 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079152 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term566 _24632 _24635 g f a) = ((term46 _24632 _24635 g f a) = a).
Proof. exact (@lem1079151 ((term46 _24632 _24635 g f a) = a)). Qed.
Lemma lem1079153 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f a) = a.
Proof. exact (EQ_MP (@lem1079152 _24632 _24635 g f a) (@lem1079149 _24632 _24635 a g f h1)). Qed.
Lemma lem1079155 {_24632 _24635 : Type'} (_17622 : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term30 _24632 _24635 P g _17622.
Proof. exact (EQ_MP (@lem1078865 _24632 _24635 P g _17622) (@lem1078864 _24632 _24635 _17622 a P g h1)). Qed.
Lemma lem1079156 {_24632 _24635 : Type'} (_17622 : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term30 _24632 _24635 P g _17622.
Proof. exact (@lem1079155 _24632 _24635 _17622 a P g h1). Qed.
Lemma lem1079157 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term568 _24632 _24635 P g f a.
Proof. exact (@lem1079156 _24632 _24635 (f a) a P g h1). Qed.
Lemma lem1079158 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term569 _24632 _24635 P g f a.
Proof. exact (fun h0 : term570 _24632 _24635 P g f a => @lem1079157 _24632 _24635 f a P g h1). Qed.
Lemma lem1079160 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079161 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term569 _24632 _24635 P g f a) = (term568 _24632 _24635 P g f a).
Proof. exact (@lem1079160 (term568 _24632 _24635 P g f a)). Qed.
Lemma lem1079162 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term568 _24632 _24635 P g f a.
Proof. exact (EQ_MP (@lem1079161 _24632 _24635 P g f a) (@lem1079158 _24632 _24635 f a P g h1)). Qed.
Lemma lem1079168 (q : Prop) (p : Prop) (r : Prop) : (term571 p q r) = (term571 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1079169 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : (term565 _24635 _17656 P _17655) = (term572 _24635 _17656 P _17655).
Proof. exact (@lem1079168 (P _17656) (term573 _24635 _17655 _17656) (term61 _24635 P _17655)). Qed.
Lemma lem1079183 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1079184 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) : (term574 _24635 _17656 P _17655) = (term575 _24635 P _17655 _17656).
Proof. exact (@lem1079183 (term61 _24635 P _17655) (term573 _24635 _17655 _17656)). Qed.
Lemma lem1079192 {_24635 : Type'} (P : _24635 -> Prop) (_17656 : _24635) : (term576 _24635 P _17656) = (term576 _24635 P _17656).
Proof. exact (eq_refl (term576 _24635 P _17656)). Qed.
Lemma lem1079193 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) : (term572 _24635 _17656 P _17655) = (term577 _24635 P _17655 _17656).
Proof. exact (MK_COMB (@lem1079192 _24635 P _17656) (@lem1079184 _24635 P _17655 _17656)). Qed.
Lemma lem1079204 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) : (term565 _24635 _17656 P _17655) = (term577 _24635 P _17655 _17656).
Proof. exact (TRANS (@lem1079169 _24635 _17656 P _17655) (@lem1079193 _24635 P _17655 _17656)). Qed.
Lemma lem1079205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1079206 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) : (term578 _24635 _17656 P _17655) = (term579 _24635 P _17655 _17656).
Proof. exact (MK_COMB (@lem1079205) (@lem1079204 _24635 P _17655 _17656)). Qed.
Lemma lem1079220 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1079221 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) : (term574 _24635 _17656 P _17655) = (term575 _24635 P _17655 _17656).
Proof. exact (@lem1079220 (term61 _24635 P _17655) (term573 _24635 _17655 _17656)). Qed.
Lemma lem1079229 {_24635 : Type'} (P : _24635 -> Prop) (_17656 : _24635) : (term576 _24635 P _17656) = (term576 _24635 P _17656).
Proof. exact (eq_refl (term576 _24635 P _17656)). Qed.
Lemma lem1079230 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) : (term572 _24635 _17656 P _17655) = (term577 _24635 P _17655 _17656).
Proof. exact (MK_COMB (@lem1079229 _24635 P _17656) (@lem1079221 _24635 P _17655 _17656)). Qed.
Lemma lem1079241 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) : ((term565 _24635 _17656 P _17655) = (term572 _24635 _17656 P _17655)) = ((term577 _24635 P _17655 _17656) = (term577 _24635 P _17655 _17656)).
Proof. exact (MK_COMB (@lem1079206 _24635 P _17655 _17656) (@lem1079230 _24635 P _17655 _17656)). Qed.
Lemma lem1079243 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1079244 (x : Prop) : (x = x) = True.
Proof. exact (@lem1079243 Prop x). Qed.
Lemma lem1079245 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) (_17656 : _24635) : ((term577 _24635 P _17655 _17656) = (term577 _24635 P _17655 _17656)) = True.
Proof. exact (@lem1079244 (term577 _24635 P _17655 _17656)). Qed.
Lemma lem1079246 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : ((term565 _24635 _17656 P _17655) = (term572 _24635 _17656 P _17655)) = True.
Proof. exact (TRANS (@lem1079241 _24635 P _17655 _17656) (@lem1079245 _24635 P _17655 _17656)). Qed.
Lemma lem1079247 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : True = ((term565 _24635 _17656 P _17655) = (term572 _24635 _17656 P _17655)).
Proof. exact (SYM (@lem1079246 _24635 _17656 P _17655)). Qed.
Lemma lem1079248 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : (term565 _24635 _17656 P _17655) = (term572 _24635 _17656 P _17655).
Proof. exact (EQ_MP (@lem1079247 _24635 _17656 P _17655) (@lem0)). Qed.
Lemma lem1079249 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : term572 _24635 _17656 P _17655.
Proof. exact (EQ_MP (@lem1079248 _24635 _17656 P _17655) (@lem1079124 _24635 _17656 P _17655)). Qed.
Lemma lem1079251 (b : Prop) (a : Prop) : (a \/ b) = (term580 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1079252 {_24635 : Type'} (_17655 : _24635) (P : _24635 -> Prop) (_17656 : _24635) : (term572 _24635 _17656 P _17655) = (term581 _24635 _17655 P _17656).
Proof. exact (@lem1079251 (term574 _24635 _17656 P _17655) (P _17656)). Qed.
Lemma lem1079254 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1079255 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : (term584 _24635 _17656 P _17655) = (term585 _24635 _17656 P _17655).
Proof. exact (@lem1079254 (term573 _24635 _17655 _17656) (term61 _24635 P _17655)). Qed.
Lemma lem1079257 (a : Prop) : (term17 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1079258 {_24635 : Type'} (_17655 : _24635) (_17656 : _24635) : (term586 _24635 _17655 _17656) = (_17655 = _17656).
Proof. exact (@lem1079257 (_17655 = _17656)). Qed.
Lemma lem1079259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1079260 {_24635 : Type'} (_17655 : _24635) (_17656 : _24635) : (term587 _24635 _17655 _17656) = (term588 _24635 _17655 _17656).
Proof. exact (MK_COMB (@lem1079259) (@lem1079258 _24635 _17655 _17656)). Qed.
Lemma lem1079262 (a : Prop) : (term17 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1079263 {_24635 : Type'} (P : _24635 -> Prop) (_17655 : _24635) : (term589 _24635 P _17655) = (P _17655).
Proof. exact (@lem1079262 (P _17655)). Qed.
Lemma lem1079264 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : (term585 _24635 _17656 P _17655) = (term590 _24635 _17656 P _17655).
Proof. exact (MK_COMB (@lem1079260 _24635 _17655 _17656) (@lem1079263 _24635 P _17655)). Qed.
Lemma lem1079265 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : (term584 _24635 _17656 P _17655) = (term590 _24635 _17656 P _17655).
Proof. exact (TRANS (@lem1079255 _24635 _17656 P _17655) (@lem1079264 _24635 _17656 P _17655)). Qed.
Lemma lem1079266 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1079267 {_24635 : Type'} (_17656 : _24635) (P : _24635 -> Prop) (_17655 : _24635) : (term591 _24635 _17656 P _17655) = (term592 _24635 _17656 P _17655).
Proof. exact (MK_COMB (@lem1079266) (@lem1079265 _24635 _17656 P _17655)). Qed.
Lemma lem1079268 {_24635 : Type'} (P : _24635 -> Prop) (_17656 : _24635) : (P _17656) = (P _17656).
Proof. exact (eq_refl (P _17656)). Qed.
Lemma lem1079269 {_24635 : Type'} (_17655 : _24635) (P : _24635 -> Prop) (_17656 : _24635) : (term581 _24635 _17655 P _17656) = (term593 _24635 _17655 P _17656).
Proof. exact (MK_COMB (@lem1079267 _24635 _17656 P _17655) (@lem1079268 _24635 P _17656)). Qed.
Lemma lem1079270 {_24635 : Type'} (_17655 : _24635) (P : _24635 -> Prop) (_17656 : _24635) : (term572 _24635 _17656 P _17655) = (term593 _24635 _17655 P _17656).
Proof. exact (TRANS (@lem1079252 _24635 _17655 P _17656) (@lem1079269 _24635 _17655 P _17656)). Qed.
Lemma lem1079272 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term267 _24632 _24635 a P g) : term594 _24632 _24635 P g f a.
Proof. exact (conj (@lem1079153 _24632 _24635 a g f h1) (@lem1079162 _24632 _24635 f a P g h2)). Qed.
Lemma lem1079274 {_24635 : Type'} (_17655 : _24635) (P : _24635 -> Prop) (_17656 : _24635) : term593 _24635 _17655 P _17656.
Proof. exact (EQ_MP (@lem1079270 _24635 _17655 P _17656) (@lem1079249 _24635 _17656 P _17655)). Qed.
Lemma lem1079275 {_24635 : Type'} (_17655 : _24635) (P : _24635 -> Prop) (_17656 : _24635) : term593 _24635 _17655 P _17656.
Proof. exact (@lem1079274 _24635 _17655 P _17656). Qed.
Lemma lem1079276 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (P : _24635 -> Prop) (a : _24635) : term595 _24632 _24635 g f P a.
Proof. exact (@lem1079275 _24635 (term46 _24632 _24635 g f a) P a). Qed.
Lemma lem1079279 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term267 _24632 _24635 a P g) : P a.
Proof. exact (@lem1079276 _24632 _24635 g f P a (@lem1079272 _24632 _24635 f a P g h1 h2)). Qed.
Lemma lem1079280 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term267 _24632 _24635 a P g) : term596 _24635 P a.
Proof. exact (fun h0 : term61 _24635 P a => @lem1079279 _24632 _24635 f a P g h1 h2). Qed.
Lemma lem1079282 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079283 {_24635 : Type'} (P : _24635 -> Prop) (a : _24635) : (term596 _24635 P a) = (P a).
Proof. exact (@lem1079282 (P a)). Qed.
Lemma lem1079284 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term267 _24632 _24635 a P g) : P a.
Proof. exact (EQ_MP (@lem1079283 _24635 P a) (@lem1079280 _24632 _24635 f a P g h1 h2)). Qed.
Lemma lem1079287 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1079289 {_24635 : Type'} (P : _24635 -> Prop) (a : _24635) : (term61 _24635 P a) = (term597 _24635 P a).
Proof. exact (@lem1079287 (P a)). Qed.
Lemma lem1079292 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term267 _24632 _24635 a P g) : term597 _24635 P a.
Proof. exact (EQ_MP (@lem1079289 _24635 P a) (@lem1078910 _24632 _24635 a P g h1)). Qed.
Lemma lem1079295 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term267 _24632 _24635 a P g) : False.
Proof. exact (@lem1079292 _24632 _24635 a P g h2 (@lem1079284 _24632 _24635 f a P g h1 h2)). Qed.
Lemma lem1079296 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term267 _24632 _24635 a P g) : term559.
Proof. exact (fun h0 : ~ False => @lem1079295 _24632 _24635 f a P g h1 h2). Qed.
Lemma lem1079298 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079299 : term559 = False.
Proof. exact (@lem1079298 False). Qed.
Lemma lem1079300 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term267 _24632 _24635 a P g) : False.
Proof. exact (EQ_MP (@lem1079299) (@lem1079296 _24632 _24635 f a P g h1 h2)). Qed.
Lemma lem1079301 {_24635 : Type'} (P : _24635 -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1079302 {_24635 : Type'} (_17661 : _24635) (_17662 : _24635) (h1 : _17661 = _17662) : _17661 = _17662.
Proof. exact (h1). Qed.
Lemma lem1079303 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) (h1 : _17661 = _17662) : (P _17661) = (P _17662).
Proof. exact (MK_COMB (@lem1079301 _24635 P) (@lem1079302 _24635 _17661 _17662 h1)). Qed.
Lemma lem1079305 (b : Prop) (a : Prop) : term560 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1079306 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : term561 _24635 _17662 P _17661.
Proof. exact (@lem1079305 (P _17662) (P _17661)). Qed.
Lemma lem1079307 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) (h1 : _17661 = _17662) : term562 _24635 _17662 P _17661.
Proof. exact (@lem1079306 _24635 _17662 P _17661 (@lem1079303 _24635 P _17661 _17662 h1)). Qed.
Lemma lem1079308 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : term563 _24635 _17662 P _17661.
Proof. exact (fun h0 : _17661 = _17662 => @lem1079307 _24635 P _17661 _17662 h0). Qed.
Lemma lem1079310 (a : Prop) (b : Prop) : (a -> b) = (term564 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1079311 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : (term563 _24635 _17662 P _17661) = (term565 _24635 _17662 P _17661).
Proof. exact (@lem1079310 (_17661 = _17662) (term562 _24635 _17662 P _17661)). Qed.
Lemma lem1079312 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : term565 _24635 _17662 P _17661.
Proof. exact (EQ_MP (@lem1079311 _24635 _17662 P _17661) (@lem1079308 _24635 _17662 P _17661)). Qed.
Lemma lem1079332 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : term598 _24635 x y z.
Proof. exact (@lem21385 _24635 x y z). Qed.
Lemma lem1079334 {_24632 _24635 : Type'} (_17624 : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f _17624) = _17624.
Proof. exact (EQ_MP (@lem1078871 _24632 _24635 g f _17624) (@lem1078870 _24632 _24635 _17624 g f h1)). Qed.
Lemma lem1079335 {_24632 _24635 : Type'} (_17624 : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f _17624) = _17624.
Proof. exact (@lem1079334 _24632 _24635 _17624 g f h1). Qed.
Lemma lem1079336 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f a) = a.
Proof. exact (@lem1079335 _24632 _24635 a g f h1). Qed.
Lemma lem1079337 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term566 _24632 _24635 g f a.
Proof. exact (fun h0 : term567 _24632 _24635 g f a => @lem1079336 _24632 _24635 a g f h1). Qed.
Lemma lem1079339 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079340 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term566 _24632 _24635 g f a) = ((term46 _24632 _24635 g f a) = a).
Proof. exact (@lem1079339 ((term46 _24632 _24635 g f a) = a)). Qed.
Lemma lem1079341 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f a) = a.
Proof. exact (EQ_MP (@lem1079340 _24632 _24635 g f a) (@lem1079337 _24632 _24635 a g f h1)). Qed.
Lemma lem1079343 {_24635 : Type'} (x : _24635) : x = x.
Proof. exact (@lem21386 _24635 x). Qed.
Lemma lem1079344 {_24635 : Type'} (x : _24635) : x = x.
Proof. exact (@lem1079343 _24635 x). Qed.
Lemma lem1079345 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term46 _24632 _24635 g f a) = (term46 _24632 _24635 g f a).
Proof. exact (@lem1079344 _24635 (term46 _24632 _24635 g f a)). Qed.
Lemma lem1079346 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : term599 _24632 _24635 g f a.
Proof. exact (fun h0 : term600 _24632 _24635 g f a => @lem1079345 _24632 _24635 g f a). Qed.
Lemma lem1079348 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079349 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term599 _24632 _24635 g f a) = ((term46 _24632 _24635 g f a) = (term46 _24632 _24635 g f a)).
Proof. exact (@lem1079348 ((term46 _24632 _24635 g f a) = (term46 _24632 _24635 g f a))). Qed.
Lemma lem1079350 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term46 _24632 _24635 g f a) = (term46 _24632 _24635 g f a).
Proof. exact (EQ_MP (@lem1079349 _24632 _24635 g f a) (@lem1079346 _24632 _24635 g f a)). Qed.
Lemma lem1079368 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1079369 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term601 _24635 x y z) = (term602 _24635 y x z).
Proof. exact (@lem1079368 (y = z) (term573 _24635 x z)). Qed.
Lemma lem1079379 {_24635 : Type'} (x : _24635) (y : _24635) : (term603 _24635 x y) = (term603 _24635 x y).
Proof. exact (eq_refl (term603 _24635 x y)). Qed.
Lemma lem1079380 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term598 _24635 x y z) = (term604 _24635 y x z).
Proof. exact (MK_COMB (@lem1079379 _24635 x y) (@lem1079369 _24635 y x z)). Qed.
Lemma lem1079384 (q : Prop) (p : Prop) (r : Prop) : (term571 p q r) = (term571 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1079385 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term604 _24635 y x z) = (term605 _24635 y x z).
Proof. exact (@lem1079384 (y = z) (term573 _24635 x y) (term573 _24635 x z)). Qed.
Lemma lem1079407 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term598 _24635 x y z) = (term605 _24635 y x z).
Proof. exact (TRANS (@lem1079380 _24635 y x z) (@lem1079385 _24635 y x z)). Qed.
Lemma lem1079408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1079409 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term606 _24635 x y z) = (term607 _24635 y x z).
Proof. exact (MK_COMB (@lem1079408) (@lem1079407 _24635 y x z)). Qed.
Lemma lem1079431 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term605 _24635 y x z) = (term605 _24635 y x z).
Proof. exact (eq_refl (term605 _24635 y x z)). Qed.
Lemma lem1079432 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : ((term598 _24635 x y z) = (term605 _24635 y x z)) = ((term605 _24635 y x z) = (term605 _24635 y x z)).
Proof. exact (MK_COMB (@lem1079409 _24635 y x z) (@lem1079431 _24635 y x z)). Qed.
Lemma lem1079434 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1079435 (x : Prop) : (x = x) = True.
Proof. exact (@lem1079434 Prop x). Qed.
Lemma lem1079436 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : ((term605 _24635 y x z) = (term605 _24635 y x z)) = True.
Proof. exact (@lem1079435 (term605 _24635 y x z)). Qed.
Lemma lem1079437 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : ((term598 _24635 x y z) = (term605 _24635 y x z)) = True.
Proof. exact (TRANS (@lem1079432 _24635 y x z) (@lem1079436 _24635 y x z)). Qed.
Lemma lem1079438 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : True = ((term598 _24635 x y z) = (term605 _24635 y x z)).
Proof. exact (SYM (@lem1079437 _24635 y x z)). Qed.
Lemma lem1079439 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term598 _24635 x y z) = (term605 _24635 y x z).
Proof. exact (EQ_MP (@lem1079438 _24635 y x z) (@lem0)). Qed.
Lemma lem1079440 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : term605 _24635 y x z.
Proof. exact (EQ_MP (@lem1079439 _24635 y x z) (@lem1079332 _24635 x y z)). Qed.
Lemma lem1079442 (b : Prop) (a : Prop) : (a \/ b) = (term580 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1079443 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : (term605 _24635 y x z) = (term608 _24635 x y z).
Proof. exact (@lem1079442 (term609 _24635 y x z) (y = z)). Qed.
Lemma lem1079445 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1079446 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term610 _24635 y x z) = (term611 _24635 y x z).
Proof. exact (@lem1079445 (term573 _24635 x y) (term573 _24635 x z)). Qed.
Lemma lem1079448 (a : Prop) : (term17 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1079449 {_24635 : Type'} (x : _24635) (y : _24635) : (term586 _24635 x y) = (x = y).
Proof. exact (@lem1079448 (x = y)). Qed.
Lemma lem1079450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1079451 {_24635 : Type'} (x : _24635) (y : _24635) : (term587 _24635 x y) = (term588 _24635 x y).
Proof. exact (MK_COMB (@lem1079450) (@lem1079449 _24635 x y)). Qed.
Lemma lem1079453 (a : Prop) : (term17 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1079454 {_24635 : Type'} (x : _24635) (z : _24635) : (term586 _24635 x z) = (x = z).
Proof. exact (@lem1079453 (x = z)). Qed.
Lemma lem1079455 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term611 _24635 y x z) = (term612 _24635 y x z).
Proof. exact (MK_COMB (@lem1079451 _24635 x y) (@lem1079454 _24635 x z)). Qed.
Lemma lem1079456 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term610 _24635 y x z) = (term612 _24635 y x z).
Proof. exact (TRANS (@lem1079446 _24635 y x z) (@lem1079455 _24635 y x z)). Qed.
Lemma lem1079457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1079458 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term613 _24635 y x z) = (term614 _24635 y x z).
Proof. exact (MK_COMB (@lem1079457) (@lem1079456 _24635 y x z)). Qed.
Lemma lem1079459 {_24635 : Type'} (y : _24635) (z : _24635) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1079460 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : (term608 _24635 x y z) = (term615 _24635 x y z).
Proof. exact (MK_COMB (@lem1079458 _24635 y x z) (@lem1079459 _24635 y z)). Qed.
Lemma lem1079461 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : (term605 _24635 y x z) = (term615 _24635 x y z).
Proof. exact (TRANS (@lem1079443 _24635 x y z) (@lem1079460 _24635 x y z)). Qed.
Lemma lem1079463 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term616 _24632 _24635 g f a.
Proof. exact (conj (@lem1079341 _24632 _24635 a g f h1) (@lem1079350 _24632 _24635 g f a)). Qed.
Lemma lem1079465 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : term615 _24635 x y z.
Proof. exact (EQ_MP (@lem1079461 _24635 x y z) (@lem1079440 _24635 y x z)). Qed.
Lemma lem1079466 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : term615 _24635 x y z.
Proof. exact (@lem1079465 _24635 x y z). Qed.
Lemma lem1079467 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : term617 _24632 _24635 g f a.
Proof. exact (@lem1079466 _24635 (term46 _24632 _24635 g f a) a (term46 _24632 _24635 g f a)). Qed.
Lemma lem1079470 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : a = (term46 _24632 _24635 g f a).
Proof. exact (@lem1079467 _24632 _24635 g f a (@lem1079463 _24632 _24635 a g f h1)). Qed.
Lemma lem1079471 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : a = (term46 _24632 _24635 g f a).
Proof. exact (@lem1079470 _24632 _24635 a g f h1). Qed.
Lemma lem1079472 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term618 _24632 _24635 g f a.
Proof. exact (fun h0 : term553 _24632 _24635 g f a => @lem1079471 _24632 _24635 a g f h1). Qed.
Lemma lem1079474 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079475 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term618 _24632 _24635 g f a) = (a = (term46 _24632 _24635 g f a)).
Proof. exact (@lem1079474 (a = (term46 _24632 _24635 g f a))). Qed.
Lemma lem1079476 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : a = (term46 _24632 _24635 g f a).
Proof. exact (EQ_MP (@lem1079475 _24632 _24635 g f a) (@lem1079472 _24632 _24635 a g f h1)). Qed.
Lemma lem1079478 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : P a.
Proof. exact (proj1 (@lem1078693 _24632 _24635 a P g h1)). Qed.
Lemma lem1079479 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : term596 _24635 P a.
Proof. exact (fun h0 : term61 _24635 P a => @lem1079478 _24632 _24635 a P g h1). Qed.
Lemma lem1079481 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079482 {_24635 : Type'} (P : _24635 -> Prop) (a : _24635) : (term596 _24635 P a) = (P a).
Proof. exact (@lem1079481 (P a)). Qed.
Lemma lem1079483 {_24632 _24635 : Type'} (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : P a.
Proof. exact (EQ_MP (@lem1079482 _24635 P a) (@lem1079479 _24632 _24635 a P g h1)). Qed.
Lemma lem1079489 (q : Prop) (p : Prop) (r : Prop) : (term571 p q r) = (term571 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1079490 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : (term565 _24635 _17662 P _17661) = (term572 _24635 _17662 P _17661).
Proof. exact (@lem1079489 (P _17662) (term573 _24635 _17661 _17662) (term61 _24635 P _17661)). Qed.
Lemma lem1079504 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1079505 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) : (term574 _24635 _17662 P _17661) = (term575 _24635 P _17661 _17662).
Proof. exact (@lem1079504 (term61 _24635 P _17661) (term573 _24635 _17661 _17662)). Qed.
Lemma lem1079513 {_24635 : Type'} (P : _24635 -> Prop) (_17662 : _24635) : (term576 _24635 P _17662) = (term576 _24635 P _17662).
Proof. exact (eq_refl (term576 _24635 P _17662)). Qed.
Lemma lem1079514 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) : (term572 _24635 _17662 P _17661) = (term577 _24635 P _17661 _17662).
Proof. exact (MK_COMB (@lem1079513 _24635 P _17662) (@lem1079505 _24635 P _17661 _17662)). Qed.
Lemma lem1079525 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) : (term565 _24635 _17662 P _17661) = (term577 _24635 P _17661 _17662).
Proof. exact (TRANS (@lem1079490 _24635 _17662 P _17661) (@lem1079514 _24635 P _17661 _17662)). Qed.
Lemma lem1079526 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1079527 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) : (term578 _24635 _17662 P _17661) = (term579 _24635 P _17661 _17662).
Proof. exact (MK_COMB (@lem1079526) (@lem1079525 _24635 P _17661 _17662)). Qed.
Lemma lem1079541 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1079542 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) : (term574 _24635 _17662 P _17661) = (term575 _24635 P _17661 _17662).
Proof. exact (@lem1079541 (term61 _24635 P _17661) (term573 _24635 _17661 _17662)). Qed.
Lemma lem1079550 {_24635 : Type'} (P : _24635 -> Prop) (_17662 : _24635) : (term576 _24635 P _17662) = (term576 _24635 P _17662).
Proof. exact (eq_refl (term576 _24635 P _17662)). Qed.
Lemma lem1079551 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) : (term572 _24635 _17662 P _17661) = (term577 _24635 P _17661 _17662).
Proof. exact (MK_COMB (@lem1079550 _24635 P _17662) (@lem1079542 _24635 P _17661 _17662)). Qed.
Lemma lem1079562 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) : ((term565 _24635 _17662 P _17661) = (term572 _24635 _17662 P _17661)) = ((term577 _24635 P _17661 _17662) = (term577 _24635 P _17661 _17662)).
Proof. exact (MK_COMB (@lem1079527 _24635 P _17661 _17662) (@lem1079551 _24635 P _17661 _17662)). Qed.
Lemma lem1079564 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1079565 (x : Prop) : (x = x) = True.
Proof. exact (@lem1079564 Prop x). Qed.
Lemma lem1079566 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) (_17662 : _24635) : ((term577 _24635 P _17661 _17662) = (term577 _24635 P _17661 _17662)) = True.
Proof. exact (@lem1079565 (term577 _24635 P _17661 _17662)). Qed.
Lemma lem1079567 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : ((term565 _24635 _17662 P _17661) = (term572 _24635 _17662 P _17661)) = True.
Proof. exact (TRANS (@lem1079562 _24635 P _17661 _17662) (@lem1079566 _24635 P _17661 _17662)). Qed.
Lemma lem1079568 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : True = ((term565 _24635 _17662 P _17661) = (term572 _24635 _17662 P _17661)).
Proof. exact (SYM (@lem1079567 _24635 _17662 P _17661)). Qed.
Lemma lem1079569 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : (term565 _24635 _17662 P _17661) = (term572 _24635 _17662 P _17661).
Proof. exact (EQ_MP (@lem1079568 _24635 _17662 P _17661) (@lem0)). Qed.
Lemma lem1079570 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : term572 _24635 _17662 P _17661.
Proof. exact (EQ_MP (@lem1079569 _24635 _17662 P _17661) (@lem1079312 _24635 _17662 P _17661)). Qed.
Lemma lem1079572 (b : Prop) (a : Prop) : (a \/ b) = (term580 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1079573 {_24635 : Type'} (_17661 : _24635) (P : _24635 -> Prop) (_17662 : _24635) : (term572 _24635 _17662 P _17661) = (term581 _24635 _17661 P _17662).
Proof. exact (@lem1079572 (term574 _24635 _17662 P _17661) (P _17662)). Qed.
Lemma lem1079575 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1079576 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : (term584 _24635 _17662 P _17661) = (term585 _24635 _17662 P _17661).
Proof. exact (@lem1079575 (term573 _24635 _17661 _17662) (term61 _24635 P _17661)). Qed.
Lemma lem1079578 (a : Prop) : (term17 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1079579 {_24635 : Type'} (_17661 : _24635) (_17662 : _24635) : (term586 _24635 _17661 _17662) = (_17661 = _17662).
Proof. exact (@lem1079578 (_17661 = _17662)). Qed.
Lemma lem1079580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1079581 {_24635 : Type'} (_17661 : _24635) (_17662 : _24635) : (term587 _24635 _17661 _17662) = (term588 _24635 _17661 _17662).
Proof. exact (MK_COMB (@lem1079580) (@lem1079579 _24635 _17661 _17662)). Qed.
Lemma lem1079583 (a : Prop) : (term17 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1079584 {_24635 : Type'} (P : _24635 -> Prop) (_17661 : _24635) : (term589 _24635 P _17661) = (P _17661).
Proof. exact (@lem1079583 (P _17661)). Qed.
Lemma lem1079585 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : (term585 _24635 _17662 P _17661) = (term590 _24635 _17662 P _17661).
Proof. exact (MK_COMB (@lem1079581 _24635 _17661 _17662) (@lem1079584 _24635 P _17661)). Qed.
Lemma lem1079586 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : (term584 _24635 _17662 P _17661) = (term590 _24635 _17662 P _17661).
Proof. exact (TRANS (@lem1079576 _24635 _17662 P _17661) (@lem1079585 _24635 _17662 P _17661)). Qed.
Lemma lem1079587 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1079588 {_24635 : Type'} (_17662 : _24635) (P : _24635 -> Prop) (_17661 : _24635) : (term591 _24635 _17662 P _17661) = (term592 _24635 _17662 P _17661).
Proof. exact (MK_COMB (@lem1079587) (@lem1079586 _24635 _17662 P _17661)). Qed.
Lemma lem1079589 {_24635 : Type'} (P : _24635 -> Prop) (_17662 : _24635) : (P _17662) = (P _17662).
Proof. exact (eq_refl (P _17662)). Qed.
Lemma lem1079590 {_24635 : Type'} (_17661 : _24635) (P : _24635 -> Prop) (_17662 : _24635) : (term581 _24635 _17661 P _17662) = (term593 _24635 _17661 P _17662).
Proof. exact (MK_COMB (@lem1079588 _24635 _17662 P _17661) (@lem1079589 _24635 P _17662)). Qed.
Lemma lem1079591 {_24635 : Type'} (_17661 : _24635) (P : _24635 -> Prop) (_17662 : _24635) : (term572 _24635 _17662 P _17661) = (term593 _24635 _17661 P _17662).
Proof. exact (TRANS (@lem1079573 _24635 _17661 P _17662) (@lem1079590 _24635 _17661 P _17662)). Qed.
Lemma lem1079593 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term368 _24632 _24635 a P g) : term619 _24632 _24635 g f P a.
Proof. exact (conj (@lem1079476 _24632 _24635 a g f h1) (@lem1079483 _24632 _24635 a P g h2)). Qed.
Lemma lem1079595 {_24635 : Type'} (_17661 : _24635) (P : _24635 -> Prop) (_17662 : _24635) : term593 _24635 _17661 P _17662.
Proof. exact (EQ_MP (@lem1079591 _24635 _17661 P _17662) (@lem1079570 _24635 _17662 P _17661)). Qed.
Lemma lem1079596 {_24635 : Type'} (_17661 : _24635) (P : _24635 -> Prop) (_17662 : _24635) : term593 _24635 _17661 P _17662.
Proof. exact (@lem1079595 _24635 _17661 P _17662). Qed.
Lemma lem1079597 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : term620 _24632 _24635 P g f a.
Proof. exact (@lem1079596 _24635 a P (term46 _24632 _24635 g f a)). Qed.
Lemma lem1079600 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term368 _24632 _24635 a P g) : term568 _24632 _24635 P g f a.
Proof. exact (@lem1079597 _24632 _24635 P g f a (@lem1079593 _24632 _24635 f a P g h1 h2)). Qed.
Lemma lem1079601 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term368 _24632 _24635 a P g) : term569 _24632 _24635 P g f a.
Proof. exact (fun h0 : term570 _24632 _24635 P g f a => @lem1079600 _24632 _24635 f a P g h1 h2). Qed.
Lemma lem1079603 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079604 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term569 _24632 _24635 P g f a) = (term568 _24632 _24635 P g f a).
Proof. exact (@lem1079603 (term568 _24632 _24635 P g f a)). Qed.
Lemma lem1079605 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term368 _24632 _24635 a P g) : term568 _24632 _24635 P g f a.
Proof. exact (EQ_MP (@lem1079604 _24632 _24635 P g f a) (@lem1079601 _24632 _24635 f a P g h1 h2)). Qed.
Lemma lem1079608 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1079610 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (_17625 : _24632) : (term68 _24632 _24635 P g _17625) = (term558 _24632 _24635 P g _17625).
Proof. exact (@lem1079608 (term30 _24632 _24635 P g _17625)). Qed.
Lemma lem1079613 {_24632 _24635 : Type'} (_17625 : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : term558 _24632 _24635 P g _17625.
Proof. exact (EQ_MP (@lem1079610 _24632 _24635 P g _17625) (@lem1078920 _24632 _24635 _17625 a P g h1)). Qed.
Lemma lem1079614 {_24632 _24635 : Type'} (_17625 : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : term558 _24632 _24635 P g _17625.
Proof. exact (@lem1079613 _24632 _24635 _17625 a P g h1). Qed.
Lemma lem1079615 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term368 _24632 _24635 a P g) : term621 _24632 _24635 P g f a.
Proof. exact (@lem1079614 _24632 _24635 (f a) a P g h1). Qed.
Lemma lem1079618 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term368 _24632 _24635 a P g) : False.
Proof. exact (@lem1079615 _24632 _24635 f a P g h2 (@lem1079605 _24632 _24635 f a P g h1 h2)). Qed.
Lemma lem1079619 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term368 _24632 _24635 a P g) : term559.
Proof. exact (fun h0 : ~ False => @lem1079618 _24632 _24635 f a P g h1 h2). Qed.
Lemma lem1079621 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079622 : term559 = False.
Proof. exact (@lem1079621 False). Qed.
Lemma lem1079623 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term368 _24632 _24635 a P g) : False.
Proof. exact (EQ_MP (@lem1079622) (@lem1079619 _24632 _24635 f a P g h1 h2)). Qed.
Lemma lem1079657 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term30 _24632 _24635 P g b.
Proof. exact (proj2 (@lem1078694 _24632 _24635 P g b h1)). Qed.
Lemma lem1079658 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term556 _24632 _24635 P g b.
Proof. exact (fun h0 : term68 _24632 _24635 P g b => @lem1079657 _24632 _24635 P g b h1). Qed.
Lemma lem1079660 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079661 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) : (term556 _24632 _24635 P g b) = (term30 _24632 _24635 P g b).
Proof. exact (@lem1079660 (term30 _24632 _24635 P g b)). Qed.
Lemma lem1079662 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term30 _24632 _24635 P g b.
Proof. exact (EQ_MP (@lem1079661 _24632 _24635 P g b) (@lem1079658 _24632 _24635 P g b h1)). Qed.
Lemma lem1079665 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1079667 {_24635 : Type'} (P : _24635 -> Prop) (_17628 : _24635) : (term61 _24635 P _17628) = (term597 _24635 P _17628).
Proof. exact (@lem1079665 (P _17628)). Qed.
Lemma lem1079670 {_24632 _24635 : Type'} (_17628 : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term597 _24635 P _17628.
Proof. exact (EQ_MP (@lem1079667 _24635 P _17628) (@lem1078926 _24632 _24635 _17628 P g b h1)). Qed.
Lemma lem1079671 {_24632 _24635 : Type'} (_17628 : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term597 _24635 P _17628.
Proof. exact (@lem1079670 _24632 _24635 _17628 P g b h1). Qed.
Lemma lem1079672 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term558 _24632 _24635 P g b.
Proof. exact (@lem1079671 _24632 _24635 (g b) P g b h1). Qed.
Lemma lem1079675 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : False.
Proof. exact (@lem1079672 _24632 _24635 P g b h1 (@lem1079662 _24632 _24635 P g b h1)). Qed.
Lemma lem1079676 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : term559.
Proof. exact (fun h0 : ~ False => @lem1079675 _24632 _24635 P g b h1). Qed.
Lemma lem1079678 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079679 : term559 = False.
Proof. exact (@lem1079678 False). Qed.
Lemma lem1079680 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term339 _24632 _24635 P g b) : False.
Proof. exact (EQ_MP (@lem1079679) (@lem1079676 _24632 _24635 P g b h1)). Qed.
Lemma lem1079702 {_24632 _24635 : Type'} (_17629 : _24632) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term49 _24632 _24635 f g _17629) = _17629.
Proof. exact (EQ_MP (@lem1078886 _24632 _24635 f g _17629) (@lem1078885 _24632 _24635 _17629 g f h1)). Qed.
Lemma lem1079703 {_24632 _24635 : Type'} (_17629 : _24632) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term49 _24632 _24635 f g _17629) = _17629.
Proof. exact (@lem1079702 _24632 _24635 _17629 g f h1). Qed.
Lemma lem1079704 {_24632 _24635 : Type'} (b : _24632) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term49 _24632 _24635 f g b) = b.
Proof. exact (@lem1079703 _24632 _24635 b g f h1). Qed.
Lemma lem1079705 {_24632 _24635 : Type'} (b : _24632) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term622 _24632 _24635 f g b.
Proof. exact (fun h0 : term547 _24632 _24635 f g b => @lem1079704 _24632 _24635 b g f h1). Qed.
Lemma lem1079707 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079708 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) (b : _24632) : (term622 _24632 _24635 f g b) = ((term49 _24632 _24635 f g b) = b).
Proof. exact (@lem1079707 ((term49 _24632 _24635 f g b) = b)). Qed.
Lemma lem1079709 {_24632 _24635 : Type'} (b : _24632) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term49 _24632 _24635 f g b) = b.
Proof. exact (EQ_MP (@lem1079708 _24632 _24635 f g b) (@lem1079705 _24632 _24635 b g f h1)). Qed.
Lemma lem1079712 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1079714 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) (b : _24632) : (term547 _24632 _24635 f g b) = (term623 _24632 _24635 f g b).
Proof. exact (@lem1079712 ((term49 _24632 _24635 f g b) = b)). Qed.
Lemma lem1079717 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term195 _24632 _24635 g f a b) : term623 _24632 _24635 f g b.
Proof. exact (EQ_MP (@lem1079714 _24632 _24635 f g b) (@lem1078999 _24632 _24635 g f a b h1)). Qed.
Lemma lem1079720 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term195 _24632 _24635 g f a b) : False.
Proof. exact (@lem1079717 _24632 _24635 g f a b h2 (@lem1079709 _24632 _24635 b g f h1)). Qed.
Lemma lem1079721 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term195 _24632 _24635 g f a b) : term559.
Proof. exact (fun h0 : ~ False => @lem1079720 _24632 _24635 g f a b h1 h2). Qed.
Lemma lem1079723 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079724 : term559 = False.
Proof. exact (@lem1079723 False). Qed.
Lemma lem1079745 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : term598 _24635 x y z.
Proof. exact (@lem21385 _24635 x y z). Qed.
Lemma lem1079747 {_24632 _24635 : Type'} (_17632 : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f _17632) = _17632.
Proof. exact (EQ_MP (@lem1078895 _24632 _24635 g f _17632) (@lem1078894 _24632 _24635 _17632 g f h1)). Qed.
Lemma lem1079748 {_24632 _24635 : Type'} (_17632 : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f _17632) = _17632.
Proof. exact (@lem1079747 _24632 _24635 _17632 g f h1). Qed.
Lemma lem1079749 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f a) = a.
Proof. exact (@lem1079748 _24632 _24635 a g f h1). Qed.
Lemma lem1079750 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term566 _24632 _24635 g f a.
Proof. exact (fun h0 : term567 _24632 _24635 g f a => @lem1079749 _24632 _24635 a g f h1). Qed.
Lemma lem1079752 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079753 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term566 _24632 _24635 g f a) = ((term46 _24632 _24635 g f a) = a).
Proof. exact (@lem1079752 ((term46 _24632 _24635 g f a) = a)). Qed.
Lemma lem1079754 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : (term46 _24632 _24635 g f a) = a.
Proof. exact (EQ_MP (@lem1079753 _24632 _24635 g f a) (@lem1079750 _24632 _24635 a g f h1)). Qed.
Lemma lem1079756 {_24635 : Type'} (x : _24635) : x = x.
Proof. exact (@lem21386 _24635 x). Qed.
Lemma lem1079757 {_24635 : Type'} (x : _24635) : x = x.
Proof. exact (@lem1079756 _24635 x). Qed.
Lemma lem1079758 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term46 _24632 _24635 g f a) = (term46 _24632 _24635 g f a).
Proof. exact (@lem1079757 _24635 (term46 _24632 _24635 g f a)). Qed.
Lemma lem1079759 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : term599 _24632 _24635 g f a.
Proof. exact (fun h0 : term600 _24632 _24635 g f a => @lem1079758 _24632 _24635 g f a). Qed.
Lemma lem1079761 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079762 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term599 _24632 _24635 g f a) = ((term46 _24632 _24635 g f a) = (term46 _24632 _24635 g f a)).
Proof. exact (@lem1079761 ((term46 _24632 _24635 g f a) = (term46 _24632 _24635 g f a))). Qed.
Lemma lem1079763 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term46 _24632 _24635 g f a) = (term46 _24632 _24635 g f a).
Proof. exact (EQ_MP (@lem1079762 _24632 _24635 g f a) (@lem1079759 _24632 _24635 g f a)). Qed.
Lemma lem1079781 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1079782 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term601 _24635 x y z) = (term602 _24635 y x z).
Proof. exact (@lem1079781 (y = z) (term573 _24635 x z)). Qed.
Lemma lem1079792 {_24635 : Type'} (x : _24635) (y : _24635) : (term603 _24635 x y) = (term603 _24635 x y).
Proof. exact (eq_refl (term603 _24635 x y)). Qed.
Lemma lem1079793 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term598 _24635 x y z) = (term604 _24635 y x z).
Proof. exact (MK_COMB (@lem1079792 _24635 x y) (@lem1079782 _24635 y x z)). Qed.
Lemma lem1079797 (q : Prop) (p : Prop) (r : Prop) : (term571 p q r) = (term571 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1079798 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term604 _24635 y x z) = (term605 _24635 y x z).
Proof. exact (@lem1079797 (y = z) (term573 _24635 x y) (term573 _24635 x z)). Qed.
Lemma lem1079820 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term598 _24635 x y z) = (term605 _24635 y x z).
Proof. exact (TRANS (@lem1079793 _24635 y x z) (@lem1079798 _24635 y x z)). Qed.
Lemma lem1079821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1079822 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term606 _24635 x y z) = (term607 _24635 y x z).
Proof. exact (MK_COMB (@lem1079821) (@lem1079820 _24635 y x z)). Qed.
Lemma lem1079844 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term605 _24635 y x z) = (term605 _24635 y x z).
Proof. exact (eq_refl (term605 _24635 y x z)). Qed.
Lemma lem1079845 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : ((term598 _24635 x y z) = (term605 _24635 y x z)) = ((term605 _24635 y x z) = (term605 _24635 y x z)).
Proof. exact (MK_COMB (@lem1079822 _24635 y x z) (@lem1079844 _24635 y x z)). Qed.
Lemma lem1079847 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1079848 (x : Prop) : (x = x) = True.
Proof. exact (@lem1079847 Prop x). Qed.
Lemma lem1079849 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : ((term605 _24635 y x z) = (term605 _24635 y x z)) = True.
Proof. exact (@lem1079848 (term605 _24635 y x z)). Qed.
Lemma lem1079850 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : ((term598 _24635 x y z) = (term605 _24635 y x z)) = True.
Proof. exact (TRANS (@lem1079845 _24635 y x z) (@lem1079849 _24635 y x z)). Qed.
Lemma lem1079851 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : True = ((term598 _24635 x y z) = (term605 _24635 y x z)).
Proof. exact (SYM (@lem1079850 _24635 y x z)). Qed.
Lemma lem1079852 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term598 _24635 x y z) = (term605 _24635 y x z).
Proof. exact (EQ_MP (@lem1079851 _24635 y x z) (@lem0)). Qed.
Lemma lem1079853 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : term605 _24635 y x z.
Proof. exact (EQ_MP (@lem1079852 _24635 y x z) (@lem1079745 _24635 x y z)). Qed.
Lemma lem1079855 (b : Prop) (a : Prop) : (a \/ b) = (term580 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1079856 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : (term605 _24635 y x z) = (term608 _24635 x y z).
Proof. exact (@lem1079855 (term609 _24635 y x z) (y = z)). Qed.
Lemma lem1079858 (a : Prop) (b : Prop) : (term582 a b) = (term583 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1079859 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term610 _24635 y x z) = (term611 _24635 y x z).
Proof. exact (@lem1079858 (term573 _24635 x y) (term573 _24635 x z)). Qed.
Lemma lem1079861 (a : Prop) : (term17 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1079862 {_24635 : Type'} (x : _24635) (y : _24635) : (term586 _24635 x y) = (x = y).
Proof. exact (@lem1079861 (x = y)). Qed.
Lemma lem1079863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1079864 {_24635 : Type'} (x : _24635) (y : _24635) : (term587 _24635 x y) = (term588 _24635 x y).
Proof. exact (MK_COMB (@lem1079863) (@lem1079862 _24635 x y)). Qed.
Lemma lem1079866 (a : Prop) : (term17 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1079867 {_24635 : Type'} (x : _24635) (z : _24635) : (term586 _24635 x z) = (x = z).
Proof. exact (@lem1079866 (x = z)). Qed.
Lemma lem1079868 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term611 _24635 y x z) = (term612 _24635 y x z).
Proof. exact (MK_COMB (@lem1079864 _24635 x y) (@lem1079867 _24635 x z)). Qed.
Lemma lem1079869 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term610 _24635 y x z) = (term612 _24635 y x z).
Proof. exact (TRANS (@lem1079859 _24635 y x z) (@lem1079868 _24635 y x z)). Qed.
Lemma lem1079870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1079871 {_24635 : Type'} (y : _24635) (x : _24635) (z : _24635) : (term613 _24635 y x z) = (term614 _24635 y x z).
Proof. exact (MK_COMB (@lem1079870) (@lem1079869 _24635 y x z)). Qed.
Lemma lem1079872 {_24635 : Type'} (y : _24635) (z : _24635) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1079873 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : (term608 _24635 x y z) = (term615 _24635 x y z).
Proof. exact (MK_COMB (@lem1079871 _24635 y x z) (@lem1079872 _24635 y z)). Qed.
Lemma lem1079874 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : (term605 _24635 y x z) = (term615 _24635 x y z).
Proof. exact (TRANS (@lem1079856 _24635 x y z) (@lem1079873 _24635 x y z)). Qed.
Lemma lem1079876 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term616 _24632 _24635 g f a.
Proof. exact (conj (@lem1079754 _24632 _24635 a g f h1) (@lem1079763 _24632 _24635 g f a)). Qed.
Lemma lem1079878 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : term615 _24635 x y z.
Proof. exact (EQ_MP (@lem1079874 _24635 x y z) (@lem1079853 _24635 y x z)). Qed.
Lemma lem1079879 {_24635 : Type'} (x : _24635) (y : _24635) (z : _24635) : term615 _24635 x y z.
Proof. exact (@lem1079878 _24635 x y z). Qed.
Lemma lem1079880 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : term617 _24632 _24635 g f a.
Proof. exact (@lem1079879 _24635 (term46 _24632 _24635 g f a) a (term46 _24632 _24635 g f a)). Qed.
Lemma lem1079883 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : a = (term46 _24632 _24635 g f a).
Proof. exact (@lem1079880 _24632 _24635 g f a (@lem1079876 _24632 _24635 a g f h1)). Qed.
Lemma lem1079884 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : a = (term46 _24632 _24635 g f a).
Proof. exact (@lem1079883 _24632 _24635 a g f h1). Qed.
Lemma lem1079885 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term618 _24632 _24635 g f a.
Proof. exact (fun h0 : term553 _24632 _24635 g f a => @lem1079884 _24632 _24635 a g f h1). Qed.
Lemma lem1079887 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079888 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term618 _24632 _24635 g f a) = (a = (term46 _24632 _24635 g f a)).
Proof. exact (@lem1079887 (a = (term46 _24632 _24635 g f a))). Qed.
Lemma lem1079889 {_24632 _24635 : Type'} (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : a = (term46 _24632 _24635 g f a).
Proof. exact (EQ_MP (@lem1079888 _24632 _24635 g f a) (@lem1079885 _24632 _24635 a g f h1)). Qed.
Lemma lem1079892 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1079894 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) : (term553 _24632 _24635 g f a) = (term624 _24632 _24635 g f a).
Proof. exact (@lem1079892 (a = (term46 _24632 _24635 g f a))). Qed.
Lemma lem1079897 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term199 _24632 _24635 g f a b) : term624 _24632 _24635 g f a.
Proof. exact (EQ_MP (@lem1079894 _24632 _24635 g f a) (@lem1079055 _24632 _24635 g f a b h1)). Qed.
Lemma lem1079900 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term199 _24632 _24635 g f a b) : False.
Proof. exact (@lem1079897 _24632 _24635 g f a b h2 (@lem1079889 _24632 _24635 a g f h1)). Qed.
Lemma lem1079901 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term199 _24632 _24635 g f a b) : term559.
Proof. exact (fun h0 : ~ False => @lem1079900 _24632 _24635 g f a b h1 h2). Qed.
Lemma lem1079903 (p : Prop) : (term557 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1079904 : term559 = False.
Proof. exact (@lem1079903 False). Qed.
Lemma lem1079906 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term199 _24632 _24635 g f a b) : False.
Proof. exact (EQ_MP (@lem1079904) (@lem1079901 _24632 _24635 g f a b h1 h2)). Qed.
Lemma lem1079907 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term195 _24632 _24635 g f a b) : False.
Proof. exact (EQ_MP (@lem1079724) (@lem1079721 _24632 _24635 g f a b h1 h2)). Qed.
Lemma lem1079908 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term120 _24632 _24635 g f a b) : False.
Proof. exact (or_elim (@lem1078692 _24632 _24635 g f a b h2) (fun h0 : term195 _24632 _24635 g f a b => @lem1079907 _24632 _24635 g f a b h1 h0) (fun h0 : term199 _24632 _24635 g f a b => @lem1079906 _24632 _24635 g f a b h1 h0)). Qed.
Lemma lem1079909 {_24632 _24635 : Type'} (f : _24635 -> _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term389 _24632 _24635 a P g b) : False.
Proof. exact (or_elim (@lem1078691 _24632 _24635 a P g b h2) (fun h0 : term368 _24632 _24635 a P g => @lem1079623 _24632 _24635 f a P g h1 h0) (fun h0 : term339 _24632 _24635 P g b => @lem1079680 _24632 _24635 P g b h0)). Qed.
Lemma lem1079910 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term455 _24632 _24635 P g f a b) : False.
Proof. exact (or_elim (@lem1078684 _24632 _24635 P g f a b h2) (fun h0 : term389 _24632 _24635 a P g b => @lem1079909 _24632 _24635 f a P g b h1 h0) (fun h0 : term120 _24632 _24635 g f a b => @lem1079908 _24632 _24635 g f a b h1 h0)). Qed.
Lemma lem1079911 {_24632 _24635 : Type'} (f : _24635 -> _24632) (x : _24632) (a : _24635) (P : _24635 -> Prop) (g : _24632 -> _24635) (h1 : term4 _24632 _24635 g f) (h2 : term319 _24632 _24635 x a P g) : False.
Proof. exact (or_elim (@lem1078683 _24632 _24635 x a P g h2) (fun h0 : term247 _24632 _24635 P g x => @lem1079112 _24632 _24635 P g x h0) (fun h0 : term267 _24632 _24635 a P g => @lem1079300 _24632 _24635 f a P g h1 h0)). Qed.
Lemma lem1079912 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term529 _24632 _24635 x P g f a b) : False.
Proof. exact (or_elim (@lem1078680 _24632 _24635 x P g f a b h2) (fun h0 : term319 _24632 _24635 x a P g => @lem1079911 _24632 _24635 f x a P g h1 h0) (fun h0 : term455 _24632 _24635 P g f a b => @lem1079910 _24632 _24635 P g f a b h1 h0)). Qed.
Lemma lem1079913 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term529 _24632 _24635 x P g f a b) : (term529 _24632 _24635 x P g f a b) = False.
Proof. exact (prop_ext (fun h3 : term529 _24632 _24635 x P g f a b => @lem1079912 _24632 _24635 x P g f a b h1 h2) (fun h3 : False => @lem1078680 _24632 _24635 x P g f a b h2)). Qed.
Lemma lem1079914 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term529 _24632 _24635 x P g f a b) : False.
Proof. exact (EQ_MP (@lem1079913 _24632 _24635 x P g f a b h1 h2) (@lem1078680 _24632 _24635 x P g f a b h2)). Qed.
Lemma lem1079915 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term529 _24632 _24635 x P g f a b) : (term4 _24632 _24635 g f) = False.
Proof. exact (prop_ext (fun h3 : term4 _24632 _24635 g f => @lem1079914 _24632 _24635 x P g f a b h1 h2) (fun h3 : False => @lem1078562 _24632 _24635 g f h1)). Qed.
Lemma lem1079916 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (a : _24635) (b : _24632) (h1 : term4 _24632 _24635 g f) (h2 : term529 _24632 _24635 x P g f a b) : False.
Proof. exact (EQ_MP (@lem1079915 _24632 _24635 x P g f a b h1 h2) (@lem1078562 _24632 _24635 g f h1)). Qed.
Lemma lem1079917 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (a : _24635) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term532 _24632 _24635 x P g f a) (h2 : term4 _24632 _24635 g f) : False.
Proof. exact (ex_elim (@lem1078533 _24632 _24635 x P g f a h1) (fun b : _24632 => fun h0 : term531 _24632 _24635 x P g f a b => @lem1079916 _24632 _24635 x P g f a b h2 h0)). Qed.
Lemma lem1079918 {_24632 _24635 : Type'} (x : _24632) (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term534 _24632 _24635 x P g f) (h2 : term4 _24632 _24635 g f) : False.
Proof. exact (ex_elim (@lem1078532 _24632 _24635 x P g f h1) (fun a : _24635 => fun h0 : term533 _24632 _24635 x P g f a => @lem1079917 _24632 _24635 x P a g f h0 h2)). Qed.
Lemma lem1079919 {_24632 _24635 : Type'} (P : _24635 -> Prop) (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term536 _24632 _24635 P g f) (h2 : term4 _24632 _24635 g f) : False.
Proof. exact (ex_elim (@lem1078531 _24632 _24635 P g f h1) (fun x : _24632 => fun h0 : term535 _24632 _24635 P g f x => @lem1079918 _24632 _24635 x P g f h0 h2)). Qed.
Lemma lem1079920 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term54 _24632 _24635 g f) (h2 : term4 _24632 _24635 g f) : False.
Proof. exact (ex_elim (@lem1078530 _24632 _24635 g f h1) (fun P : _24635 -> Prop => fun h0 : term537 _24632 _24635 g f P => @lem1079919 _24632 _24635 P g f h0 h2)). Qed.
Lemma lem1079921 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term54 _24632 _24635 g f) (h2 : term4 _24632 _24635 g f) : (term4 _24632 _24635 g f) = False.
Proof. exact (prop_ext (fun h3 : term4 _24632 _24635 g f => @lem1079920 _24632 _24635 g f h1 h2) (fun h3 : False => @lem1077276 _24632 _24635 g f h2)). Qed.
Lemma lem1079922 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term54 _24632 _24635 g f) (h2 : term4 _24632 _24635 g f) : False.
Proof. exact (EQ_MP (@lem1079921 _24632 _24635 g f h1 h2) (@lem1077276 _24632 _24635 g f h2)). Qed.
Lemma lem1079923 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term54 _24632 _24635 g f) (h2 : term4 _24632 _24635 g f) : (term54 _24632 _24635 g f) = False.
Proof. exact (prop_ext (fun h3 : term54 _24632 _24635 g f => @lem1079922 _24632 _24635 g f h1 h2) (fun h3 : False => @lem1077252 _24632 _24635 g f h1)). Qed.
Lemma lem1079924 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term54 _24632 _24635 g f) (h2 : term4 _24632 _24635 g f) : False.
Proof. exact (EQ_MP (@lem1079923 _24632 _24635 g f h1 h2) (@lem1077252 _24632 _24635 g f h1)). Qed.
Lemma lem1079925 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term53 _24632 _24635 g f.
Proof. exact (fun h0 : term54 _24632 _24635 g f => @lem1079924 _24632 _24635 g f h0 h1). Qed.
Lemma lem1079926 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term4 _24632 _24635 g f) : term7 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1077251 _24632 _24635 g f) (@lem1079925 _24632 _24635 g f h1)). Qed.
Lemma lem1079927 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term9 _24632 _24635 g f.
Proof. exact (fun h0 : term4 _24632 _24635 g f => @lem1079926 _24632 _24635 g f h0). Qed.
Lemma lem1079932 {_24632 _24635 : Type'} (f : _24635 -> _24632) : term21 _24632 _24635 f.
Proof. exact (fun g : _24632 -> _24635 => @lem1079927 _24632 _24635 g f). Qed.
Lemma lem1079937 {_24632 _24635 : Type'} : term25 _24632 _24635.
Proof. exact (fun f : _24635 -> _24632 => @lem1079932 _24632 _24635 f). Qed.
Lemma lem1079938 {_24632 _24635 : Type'} : term24 _24632 _24635.
Proof. exact (EQ_MP (@lem1077246 _24632 _24635) (@lem1079937 _24632 _24635)). Qed.
Lemma lem1079939 {_24632 _24635 : Type'} (f : _24635 -> _24632) : term625 _24632 _24635 f.
Proof. exact (@lem1079938 _24632 _24635 f). Qed.
Lemma lem1079940 {_24632 _24635 : Type'} (f : _24635 -> _24632) : (term625 _24632 _24635 f) = (term20 _24632 _24635 f).
Proof. exact (eq_refl (term625 _24632 _24635 f)). Qed.
Lemma lem1079941 {_24632 _24635 : Type'} (f : _24635 -> _24632) : term20 _24632 _24635 f.
Proof. exact (EQ_MP (@lem1079940 _24632 _24635 f) (@lem1079939 _24632 _24635 f)). Qed.
Lemma lem1079942 {_24632 _24635 : Type'} (f : _24635 -> _24632) (g : _24632 -> _24635) : term626 _24632 _24635 f g.
Proof. exact (@lem1079941 _24632 _24635 f g). Qed.
Lemma lem1079943 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : (term626 _24632 _24635 f g) = (term11 _24632 _24635 g f).
Proof. exact (eq_refl (term626 _24632 _24635 f g)). Qed.
Lemma lem1079944 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term11 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1079943 _24632 _24635 g f) (@lem1079942 _24632 _24635 f g)). Qed.
Lemma lem1079946 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term11 _24632 _24635 g f.
Proof. exact (@lem1077016 _24632 _24635 g f (@lem1079944 _24632 _24635 g f)). Qed.
Lemma lem1079947 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term12 _24632 _24635 g f) : False.
Proof. exact (@lem1079946 _24632 _24635 g f (@lem1077000 _24632 _24635 g f h1)). Qed.
Lemma lem1079948 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term12 _24632 _24635 g f) : (term12 _24632 _24635 g f) = False.
Proof. exact (prop_ext (fun h2 : term12 _24632 _24635 g f => @lem1079947 _24632 _24635 g f h1) (fun h2 : False => @lem1077000 _24632 _24635 g f h1)). Qed.
Lemma lem1079949 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) (h1 : term12 _24632 _24635 g f) : False.
Proof. exact (EQ_MP (@lem1079948 _24632 _24635 g f h1) (@lem1077000 _24632 _24635 g f h1)). Qed.
Lemma lem1079950 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term11 _24632 _24635 g f.
Proof. exact (fun h0 : term12 _24632 _24635 g f => @lem1079949 _24632 _24635 g f h0). Qed.
Lemma lem1079951 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term9 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1076999 _24632 _24635 g f) (@lem1079950 _24632 _24635 g f)). Qed.
Lemma lem1079952 {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632) : term8 _24632 _24635 g f.
Proof. exact (EQ_MP (@lem1076995 _24632 _24635 g f) (@lem1079951 _24632 _24635 g f)). Qed.
