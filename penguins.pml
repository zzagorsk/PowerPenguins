#define NORTH 0
#define EAST 1
#define SOUTH 2
#define WEST 3

#define OFF_BOARD -1
#define BOARD_SIZE 3
#define CENTER (BOARD_SIZE / 2)
#define MAX_MOVE 5
#define NUM_PENGUINS 4
#define WIN_COND 3

#define EARMUFFS 0
#define SNOWSHOES 1
#define SLINGSHOT 2
#define NUM_CARDS 3

#define INFINITY 5

typedef Point {
	short x;
    short y;
}

typedef Penguin {
	Point curr_pos;
	byte dir;
	short health;
	byte points;
	Point home;
	bool stunned;
	bool has_snowball;
	bool has_card[NUM_CARDS];
	bool using_card[NUM_CARDS];
    bool has_used_card[NUM_CARDS];
}

Penguin penguins[NUM_PENGUINS];
bool game_over = false;
bool ltl_okay = false;

inline move() {
	byte p;
	byte move_dists[NUM_PENGUINS];
	byte snowshoe_dirs[NUM_PENGUINS];
	for (p in move_dists) {
		byte j;
		select (j : 0 .. MAX_MOVE);
		move_dists[p] = j;
		select (j : NORTH .. WEST);
		snowshoe_dirs[p] = j;	
	}

	skip;
	d_step {
		for (p in penguins) {
			if
			:: !penguins[p].stunned ->
				max_move_dist(penguins[p], move_dists[p]);
				move_penguin(penguins[p], move_dists[p]);
				printf("Penguin %d moved %d spaces to (%d, %d)\n", 
				       p, move_dists[p], penguins[p].curr_pos.x, 
				       penguins[p].curr_pos.y);
				assert(!(penguins[p].curr_pos.x == CENTER &&
				         penguins[p].curr_pos.y == CENTER));
			:: else
			fi;
		}
	
		for (p in penguins) {
			if
			:: penguins[p].using_card[SNOWSHOES] ->
				bool in_bounds;
				Point next_pos;
				do
				::
					relocate(next_pos, penguins[p].curr_pos);
					if
					:: snowshoe_dirs[p] == NORTH ->
						next_pos.y--;
					:: snowshoe_dirs[p] == EAST  ->
						next_pos.x++;
					:: snowshoe_dirs[p] == SOUTH ->
						next_pos.y++;
					:: snowshoe_dirs[p] == WEST  ->
						next_pos.x--;
					fi;
					check_in_bounds(next_pos, in_bounds);
					if
					:: in_bounds ->
						relocate(penguins[p].curr_pos, next_pos);
						break;
					:: else ->
						snowshoe_dirs[p] = (snowshoe_dirs[p] + 1) % 4
					fi;
				od;
				penguins[p].using_card[SNOWSHOES] = false;
                penguins[p].has_used_card[SNOWSHOES] = true;
			:: else
			fi;
		}
		check_collisions()
	}
	
}

inline max_move_dist(p, dist) {
	if
	:: p.dir == NORTH ->
		min(p.curr_pos.y, dist, dist);
	:: p.dir == EAST  ->
		min((BOARD_SIZE - p.curr_pos.x - 1), dist, dist);
	:: p.dir == SOUTH ->
		min((BOARD_SIZE - p.curr_pos.y - 1), dist, dist);
	:: p.dir == WEST  ->
		min(p.curr_pos.x, dist, dist);
	fi;
}

inline min(a, b, ret) {
	if 
	:: a < b -> ret = a;
	:: else  -> ret = b;
	fi;
}

inline move_penguin(p, dist) {
	if
	:: p.dir == NORTH -> 
		if
		:: p.curr_pos.x == CENTER && p.curr_pos.y > CENTER && 
		   p.curr_pos.y - dist < CENTER ->
			dist--;
        :: else
		fi;
		if
		:: p.curr_pos.x == CENTER && p.curr_pos.y - dist == CENTER -> 
			dist--;
        :: else
		fi;
		p.curr_pos.y = p.curr_pos.y - dist;
	:: p.dir == EAST  -> 
		if
		:: p.curr_pos.y == CENTER && p.curr_pos.x < CENTER && 
		   p.curr_pos.x + dist > CENTER ->
			dist--;
        :: else
		fi;
		if
		:: p.curr_pos.y == CENTER && p.curr_pos.x + dist == CENTER -> 
			dist--;
        :: else
		fi;
		p.curr_pos.x = p.curr_pos.x + dist;
	:: p.dir == SOUTH -> 
		if
		:: p.curr_pos.x == CENTER && p.curr_pos.y < CENTER && 
		   p.curr_pos.y + dist > CENTER ->
			dist--;
        :: else
		fi;
		if
		:: p.curr_pos.x == CENTER && p.curr_pos.y + dist == CENTER -> 
			dist--;
        :: else
		fi;
		p.curr_pos.y = p.curr_pos.y + dist;
	:: p.dir == WEST  -> 
		if
		:: p.curr_pos.y == CENTER && p.curr_pos.x > CENTER && 
		   p.curr_pos.x - dist < CENTER ->
			dist--;
        :: else
		fi;
		if
		:: p.curr_pos.y == CENTER && p.curr_pos.x - dist == CENTER -> 
			dist--;
        :: else
		fi;
		p.curr_pos.x = p.curr_pos.x - dist;
	fi; 
}

inline check_collisions() {
	byte m;
	for (m in penguins){
		byte n;
		for (n in penguins){
			bool collision;
			check_collision(penguins[m].curr_pos, penguins[n].curr_pos, collision)
			if
			:: collision && m > n ->
				penguins[m].health--;
				penguins[m].has_snowball = false;
				penguins[n].health--;
				penguins[n].has_snowball = false;
			:: else
			fi;
		}
	}
	stun_only_cleanup()
}


inline shoot() {
	byte p;
	byte shoot_dirs[NUM_PENGUINS];
	for (p in penguins){
		byte dir;
		select (dir : NORTH .. WEST);
		shoot_dirs[p] = dir;
	}
	skip;
	d_step {
		for (p in penguins){
			if
			:: penguins[p].has_snowball ->
				Point snowball;
				snowball.x = penguins[p].curr_pos.x;
				snowball.y = penguins[p].curr_pos.y;
				penguins[p].has_snowball = false;
				bool in_bounds;
				bool penguin_hit = false;
				do ::
					if
					:: penguins[p].using_card[SLINGSHOT] ->
						move_snowball_diag(snowball, shoot_dirs[p]);
					:: else ->
						move_snowball(snowball, shoot_dirs[p]);
					fi;
					check_in_bounds(snowball, in_bounds);
					if
					//:: !in_bounds || penguin_hit -> break;
					:: !in_bounds -> break;
					:: else -> 
						byte i;
						for (i in penguins) {	
							bool collision;
							check_collision(snowball, penguins[i].curr_pos, collision)
							if
							:: collision && !penguins[i].stunned -> 
								penguins[p].points++;
								penguins[i].health--;
								//penguin_hit = true;
							:: else
							fi;
						}
					fi;
				od;
                if
                :: penguins[p].using_card[SLINGSHOT] ->
				    penguins[p].using_card[SLINGSHOT] = false;
                    penguins[p].has_used_card[SLINGSHOT] = true;
                :: else
                fi;
			:: else
			fi
		}
	}
}

inline move_snowball(s, dir){
	if
	:: dir == NORTH ->
		s.y--;
	:: dir == SOUTH ->
		s.y++;
	:: dir == EAST  ->
		s.x++;
	:: dir == WEST  ->
		s.x--;
	fi;
}

inline move_snowball_diag(s, dir){
	if
	:: dir == NORTH ->
		s.y--;
		s.x++;
	:: dir == SOUTH ->
		s.y++;
		s.x--;
	:: dir == EAST  ->
		s.x++;
		s.y++;
	:: dir == WEST  ->
		s.x--;
		s.y--;
	fi;
}

inline check_in_bounds(s, ret){
	ret = s.x >= 0 && s.x < BOARD_SIZE && s.y >= 0 && s.y < BOARD_SIZE &&
	      (s.x != CENTER || s.y != CENTER);
}

inline check_collision(p1, p2, ret){
	ret = p1.x == p2.x && p1.y == p2.y;
}

inline turn() {
	byte p;
	for (p in penguins){ 
		byte dir;
		select (dir : NORTH .. WEST);
		penguins[p].dir = dir;
	}
}

inline stun_only_cleanup() {
	byte z;
	for (z in penguins){
		if
		:: penguins[z].health <= 0 ->
			penguins[z].stunned = true;
		:: else
		fi;
	}
}

inline big_cleanup() {
	d_step {
		byte z;
		for (z in penguins){
			if
			:: penguins[z].health <= 0 && penguins[z].curr_pos.x != OFF_BOARD ->
				penguins[z].stunned = true;
				penguins[z].curr_pos.x = OFF_BOARD;
				penguins[z].curr_pos.y = OFF_BOARD;
				penguins[z].has_snowball = false;
			:: penguins[z].stunned && penguins[z].curr_pos.x == OFF_BOARD ->
				relocate(penguins[z].curr_pos, penguins[z].home);
				penguins[z].has_snowball = true;
				penguins[z].health = 3;
				penguins[z].stunned = false;
			:: else -> //not stunned, on board
				penguins[z].has_snowball = true;
			fi;
		}
	}
}

inline check_victory() {
	d_step {
		byte p;
		byte max_points = 0;
	    byte max_count = 0;
		for (p in penguins){
			if
			:: penguins[p].points > max_points ->
				max_count = 1;
				max_points = penguins[p].points;
			:: penguins[p].points == max_points ->
				max_count++;
			:: else
			fi;
		}
		if
		:: max_points >= WIN_COND && max_count == 1 ->
			game_over = true;
		:: max_points > INFINITY ->
			assert(false)
		:: else
		fi;
	}
}

inline setup(p){
	penguins[p].stunned = false;
	penguins[p].health = 3;
	penguins[p].has_snowball = true;
	penguins[p].points = 0;
	penguins[p].dir = p;
    byte i;
	for (i : 0 .. NUM_CARDS - 1){
		penguins[p].has_card[i] = true;
		penguins[p].using_card[i] = false;
        penguins[p].has_used_card[i] = false;
	}
	if
	:: p == NORTH ->
		penguins[p].home.x = CENTER;
		penguins[p].home.y = BOARD_SIZE - 1;
	:: p == SOUTH ->
		penguins[p].home.x = CENTER;
		penguins[p].home.y = 0;
	:: p == EAST ->
		penguins[p].home.x = BOARD_SIZE - 1;
		penguins[p].home.y = CENTER;
	:: p == WEST ->
		penguins[p].home.x = 0;
		penguins[p].home.y = CENTER;
	fi;
	relocate(penguins[p].curr_pos, penguins[p].home);
}

inline relocate(old_pos, new_pos){
	old_pos.x = new_pos.x;
	old_pos.y = new_pos.y;
}

inline pick_cards(){
	byte p;
	byte cards[NUM_PENGUINS];
	for (p in cards) {
		byte card;
		select (card : 0 .. NUM_CARDS);
		cards[p] = card;
	}
	skip;
	d_step {
		for (p in penguins) {
			if 
			:: cards[p] < NUM_CARDS && penguins[p].has_card[cards[p]]->
				penguins[p].has_card[cards[p]] = false;
				penguins[p].using_card[cards[p]] = true;
			:: else
			fi;
		}
		
		//Use EARMUFFS card if selected.
		for (p in penguins) {
			if
			:: penguins[p].using_card[EARMUFFS] ->
				penguins[p].health++;
				penguins[p].using_card[EARMUFFS] = false;
				penguins[p].has_used_card[EARMUFFS] = true;
			:: else
			fi;
		}
	}
}

active proctype game () {
	//Instantiate penguins.
	d_step {
		byte p;
		for (p in penguins){
			setup(p);
		}
	}
	ltl_okay = true;
	do
	:: game_over ->
		break;
	:: else ->
    	ltl_okay = false;
		pick_cards();
		move();
		shoot();
		big_cleanup();
		turn();
		check_victory();
		ltl_okay = true;
	od;
}

//LTL Assertions
//Points strictly increase.
//Always possible to reach a winning state.

//Penguins on board XOR stunned.
ltl on_board_or_stunned { always (ltl_okay implies
    ((penguins[0].curr_pos.x >= 0 && 
      penguins[0].curr_pos.y >= 0 &&
      penguins[0].curr_pos.x < BOARD_SIZE && 
      penguins[0].curr_pos.y < BOARD_SIZE &&
     !penguins[0].stunned) ||
     (penguins[0].curr_pos.x == OFF_BOARD &&
      penguins[0].curr_pos.y == OFF_BOARD &&
      penguins[0].stunned)) &&
    ((penguins[1].curr_pos.x >= 0 && 
      penguins[1].curr_pos.y >= 0 &&
      penguins[1].curr_pos.x < BOARD_SIZE && 
      penguins[1].curr_pos.y < BOARD_SIZE &&
     !penguins[1].stunned) ||
     (penguins[1].curr_pos.x == OFF_BOARD &&
      penguins[1].curr_pos.y == OFF_BOARD &&
      penguins[1].stunned)) &&
    ((penguins[2].curr_pos.x >= 0 && 
      penguins[2].curr_pos.y >= 0 &&
      penguins[2].curr_pos.x < BOARD_SIZE && 
      penguins[2].curr_pos.y < BOARD_SIZE &&
     !penguins[2].stunned) ||
     (penguins[2].curr_pos.x == OFF_BOARD &&
      penguins[2].curr_pos.y == OFF_BOARD &&
      penguins[2].stunned)) &&
    ((penguins[3].curr_pos.x >= 0 && 
      penguins[3].curr_pos.y >= 0 &&
      penguins[3].curr_pos.x < BOARD_SIZE && 
      penguins[3].curr_pos.y < BOARD_SIZE &&
     !penguins[3].stunned) ||
     (penguins[3].curr_pos.x == OFF_BOARD &&
      penguins[3].curr_pos.y == OFF_BOARD &&
      penguins[3].stunned))) 
}

ltl stunned_or_healthy { always (ltl_okay implies
    ((penguins[0].stunned && penguins[0].health <= 0) ||
    (!penguins[0].stunned && penguins[0].health > 0)) &&
    ((penguins[1].stunned && penguins[1].health <= 0) ||
    (!penguins[1].stunned && penguins[1].health > 0)) &&
    ((penguins[2].stunned && penguins[2].health <= 0) ||
    (!penguins[2].stunned && penguins[2].health > 0)) &&
    ((penguins[3].stunned && penguins[3].health <= 0) ||
    (!penguins[3].stunned && penguins[3].health > 0)))
}

//We can show that it is possible to have infinite gameplay.
ltl game_can_end { always (eventually game_over) }

//Every penguin either has one of each card or has used that card.
ltl no_card_reuse { always (ltl_okay implies
    ((penguins[0].has_card[0] == !penguins[0].has_used_card[0]) &&
    (penguins[0].has_card[1] == !penguins[0].has_used_card[1]) &&
    (penguins[0].has_card[2] == !penguins[0].has_used_card[2]) &&
    (penguins[1].has_card[0] == !penguins[1].has_used_card[0]) &&
    (penguins[1].has_card[1] == !penguins[1].has_used_card[1]) &&
    (penguins[1].has_card[2] == !penguins[1].has_used_card[2]) &&
    (penguins[2].has_card[0] == !penguins[2].has_used_card[0]) &&
    (penguins[2].has_card[1] == !penguins[2].has_used_card[1]) &&
    (penguins[2].has_card[2] == !penguins[2].has_used_card[2]) &&
    (penguins[3].has_card[0] == !penguins[3].has_used_card[0]) &&
    (penguins[3].has_card[1] == !penguins[3].has_used_card[1]) &&
    (penguins[3].has_card[2] == !penguins[3].has_used_card[2])))}
