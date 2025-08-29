import random
from enum import Enum

class LandTypes(Enum):
    AA = 0
    INFANTRY = 1
    ARTILLERY = 2
    MECH_INFANTRY = 3
    TANK = 4

class SeaTypes(Enum):
    TRANSPORT = 0
    SUBMARINE = 1
    DESTROYER = 2
    CRUISER = 3
    AC_CARRIER = 4
    BATTLESHIP = 5

class AirTypes(Enum):
    FIGHTER = 0
    TACT_BOMBER = 1
    STRAT_BOMBER = 2

class PriorityTypes(Enum):
    ATTACK = 0
    DEFENSE = 1
    COST = 2

class Unit:
    def __init__(self, unit_type, cost, attack, defense, move, max_hits, opening_fire):
        self.name = unit_type.name
        self.priority = unit_type.value
        self.cost = cost
        self.attack = attack
        self.defense = defense
        self.move = move
        self.max_hits = max_hits
        self.hit_points = max_hits
        self.opening_fire = opening_fire # Boolean if unit allows for opening fire

    def roll_attack(self):
        roll_val = random.randint(1,6)
        if roll_val <= self.attack:
            return 1
        else:
            return 0

    def roll_defense(self):
        roll_val = random.randint(1,6)
        if roll_val <= self.defense:
            return 1
        else:
            return 0

    def is_dead(self):
        # Kill units with sufficient hit-points, ignore 0-hit-point units (i.e. transports)
        if self.hit_points >= self.max_hits > 0:
            return True
        else:
            return False

    def assign_hit(self):
        if not self.is_dead():
            self.hit_points += 1
            return True
        else:
            return False

class Army:
    def __init__(self, nation, zone):
        self.nation = nation
        self.zone = zone
        self.unit_list = []

    def add_unit(self, new_unit):
        self.unit_list.append(new_unit)

    def sort_unit_list(self, sort_priority_1, sort_priority_2):

        # Sort lists in ascending order by [attack, defense, cost] value
        if sort_priority_1.name == 'ATTACK':
            self.unit_list.sort(key=lambda p: (p.attack, p.cost))
        elif sort_priority_1.name == 'DEFENSE':
            self.unit_list.sort(key=lambda p: (p.defense, p.cost))
        elif sort_priority_1.name == 'COST' and sort_priority_2.name == 'ATTACK':
            self.unit_list.sort(key=lambda p: (p.cost, p.attack))
        elif sort_priority_1.name == 'COST' and sort_priority_2.name == 'DEFENSE':
            self.unit_list.sort(key=lambda p: (p.cost, p.defense))
        else:
            return False
        return True

    def attack(self):
        num_hits = 0
        for unit in self.unit_list:
            num_hits += unit.roll_attack()
        return num_hits

    def defend(self):
        num_hits = 0
        for unit in self.unit_list:
            num_hits += unit.roll_defense()
        return num_hits

    def assign_hits(self, num_hits):
        remaining_hits = num_hits

        # Add hits to units with multiple hit-points first
        for unit in self.unit_list:
            if remaining_hits > 0 and (unit.max_hits > unit.hit_points + 1):
                unit.assign_hit()
                remaining_hits -= 1

        # Add hits to units in order of priority
        for unit in self.unit_list:
            if remaining_hits > 0 and unit.assign_hit():
                remaining_hits -= 1

    def remove_units(self):
        num_killed = 0
        cost_killed = 0
        for unit in self.unit_list:
            if unit.is_dead():
                num_killed += 1
                cost_killed += unit.cost
                self.unit_list.remove(unit)
        return num_killed, cost_killed

class Battle:
    def __init__(self, attacker, defender, attack_priority_1, attack_priority_2, defend_priority_1, defend_priority_2):
        self.attacker = attacker
        self.defender = defender

        # Sort attacker and defender units for casualty priority
        self.attacker.sort_unit_list(attack_priority_1, attack_priority_2)
        self.defender.sort_unit_list(defend_priority_1, defend_priority_2)

    def combat_round(self):
        # Attacker combat roll
        attack_hit_points = self.attacker.attack()
        self.defender.assign_hits(attack_hit_points)

        # Defender combat roll
        defense_hit_points = self.defender.defend()
        self.defender.assign_hits(defense_hit_points)

        # Remove Casualties
        self.attacker.remove_units()
        self.defender.remove_units()

        # Check for victory


unit_infantry = Unit(LandTypes.INFANTRY, 3, 1, 2, 1, 1, False)
