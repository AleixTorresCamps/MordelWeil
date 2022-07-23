import data.real.basic
import group_theory.finiteness
import algebra.group.defs

noncomputable theory

open set
open group
open subgroup
open add_group

-- Let G be a group and S the set of representants of G/mG
variables {G : Type*} [add_comm_group G]

def fin_quotient (S : set G) [finite S] (m : ℕ):= -- m ≥ 2
  ∀ g : G, ∃ g₀ ∈ S, ∃ h : G, g = g₀ + m•h

variables {S : set G} [finite S]

-- Heights formulated with a general m
class height (ht : G → ℝ) :=
-- (nonneg : ∀ g : G, 0 ≤ ht g)
(C₁ : G → ℝ)
(upper_bound : ∀ g₀ : G, ∀ g : G, ht(g₀ + g) ≤ 2*ht g  + C₁ g₀)
(m : ℕ) (Hm : m ≥ 2)
(C₂ : ℝ)
(lower_bound : ∀ g : G, ht (m•g) ≥ (m^2)*(ht g) + C₂)
(finite_boxes : ∀ C₃ : ℝ, {g : G | ht g ≤ C₃}.finite)

variables (ht : G → ℝ) [height ht]

-- let C := max{C₁ Q | Q : S} + C₂
-- def C [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) : ℝ :=
--   ((height.C₁ ht ''S).to_finset.max' (set.nonempty.image (height.C₁ ht) hS)) + height.C₂ ht
def C [fintype S] (hS : S.nonempty) (h : fin_quotient S (height.m ht)) : ℝ :=
begin
  let R := height.C₁ ht ''S,
  have hip : R.finite,
  exact to_finite R,

  have R_ne : R.to_finset.nonempty,
  {
  choose s Hs using hS,
  use (height.C₁ ht s),
  simp,
  use s,
  split,
  exact Hs,
  refl,  
  },

  exact (R.to_finset.max' R_ne) + height.C₂ ht,
end

-- finite.set.finite_of_finite_image


-- This C has two important properties that combine C₁ and C₂
lemma useful_C (hS : nonempty S.to_finset) (h : fin_quotient S (height.m ht)) (g₀ : S) (g : G):
(ht (g - g₀) ≤ ht (2•g) + C)
:=
begin
  sorry
end


lemma useful_C' (h : fin_quotient S (height.m ht)) (g₀ : S) (g : G) :
(∀ g : G, ht ((height.m ht)•g) ≥ ((height.m ht)^2)*(ht g) + C)
:=
begin
  sorry
end

-- Set of generators: S ∪ {g : G | ht g ≤ C}
def U : set G :=
begin
  exact S ∪ {g : G | ht g ≤ C}
end


def seq_P (P : G) : ℕ → G :=
begin
  sorry,

  -- Idea de la seqüencia:
  -- seq_P 0 = P
  -- seq_P succ n := el Q : G tal que seq_P n - Qₐ{iₙ} = mQ
end


-- Falta lemma diferents altures => diferents punts ?
-- Falten lemmes que reescriuen les desigualtats com s'utilitzen

lemma elem_with_height_less_C (P : G) :
∃ Pⱼ : seq_P P, ht Q ≤ C :=
begin
  sorry

  -- Idea de la demo:
  -- Suposem el contrari
  -- Llavors per les desigualtats veiem que l'altura es va fent petita (altres lemmes?)
  -- Dir que tots els punts son diferents
  -- Dir que el conjunt de punts amb altura  ≤ ht P és infinit
  -- Arribem a contradicció 
end


-- Descent theorem
lemma main_theorem (S : set G) [finite S] (m : ℕ) (Hm : m ≥ 2) (h : fin_quotient S m) 
(ht : G → ℝ) [height ht] : 
fg G :=
begin
  rw add_group.fg_iff,

  
  -- Usar el lema usefull_C per obtenir la C
  -- Donar el subconjunt generador S ∪ {g : G | ht g ≤ C} (per propietats és finit)
  -- A partir d'aquí no entenc com funciona...
  -- Donat un P
  -- Definim la seq. {P_j} (amb les seves definicions/hipotesis) 
  -- Veiem que dins de la seq. hi ha elements d'altura ≤ C, diem-li Pⱼ
  -- S'ha d veure que podem escriure P com a combinació de Qᵢ i algun Pⱼ
  -- Ho usem pel Pⱼ que té altura ≤ C
  
  sorry
end





