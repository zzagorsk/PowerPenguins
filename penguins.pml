#define NORTH 1
#define EAST 2
#define SOUTH 3
#define WEST 4

#define BOARD_SIZE 7
#define MAX_MOVE 5
#define NUM_PENGUINS 4

typedef Point {
	int x;
	int y;
}

typedef Penguin {
	Point currPos;
	int dir;
	int health;
	int points;
	Point home;
	bool stunned;
}

Penguin penguins[NUM_PENGUINS];


inline move() {
	int i;
	for (i in penguins) {
		int max_dist;
		max_move_dist(penguins[i], max_dist);
		int dist;
		select (dist : 0 .. max_dist);
		move_penguin(penguins[i], dist)
	}
	//check_collisions();
}

inline max_move_dist(p, dist) {
	if
	:: p.dir == NORTH ->
		max(p.currPos.y, MAX_MOVE, dist);
	:: p.dir == EAST  ->
		max((BOARD_SIZE - p.currPos.x), MAX_MOVE, dist);
	:: p.dir == SOUTH ->
		max((BOARD_SIZE - p.currPos.y), MAX_MOVE, dist);
	:: p.dir == WEST  ->
		max(p.currPos.x, MAX_MOVE, dist);
	fi;
}

inline move_penguin(p, dist) {
	if
	:: p.dir == NORTH -> 
		p.currPos.y = p.currPos.y - dist;
	:: p.dir == EAST  -> 
		p.currPos.x = p.currPos.x + dist;
	:: p.dir == SOUTH -> 
		p.currPos.y = p.currPos.y + dist;
	:: p.dir == WEST  -> 
		p.currPos.x = p.currPos.x - dist;
	fi; 
}
	
inline max(a, b, ret) {
	if 
	:: a > b -> ret = a;
	:: else  -> ret = b;
	fi;
}

/*
inline check_collisions() {
	//perform collision checks
}
*/

inline shoot() {
	int i;
	for (i in penguins){
		int shoot_dir;
		select (shoot_dir : 1 .. 4);
		Point snowball;
		snowball.x = penguins[i].currPos.x;
		snowball.y = penguins[i].currPos.y;
		bool in_bounds;
		do ::
			move_snowball(snowball, shoot_dir);
			check_in_bounds(snowball, in_bounds);
			if
			:: !in_bounds -> break;
			:: else -> 
				int j;
				for (j in penguins) {	
					bool collision;
					check_collision(snowball, penguins[j].currPos, collision)
					if
					:: collision -> 
						penguins[i].points++;
						penguins[j].health--;
					:: else
					fi;
				}
			fi;
		od;
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

inline check_in_bounds(s, ret){
	ret = s.x >= 0 && s.x < BOARD_SIZE && s.y >= 0 && s.y < BOARD_SIZE;
}

inline check_collision(p1, p2, ret){
	ret = p1.x == p2.x && p1.y == p2.y;
}

inline turn() {
	int i;
	for (i in penguins){
		int turn_dir;
		select (turn_dir : 1 .. 4);
		penguins[i].dir = turn_dir;
	}
}

active proctype game () {
	//Instantiate penguins.

	do
	:: move();
	   shoot();
	   //cleanup();
	   turn();
	od;
}

//LTL Assertions
//Penguins are on board.
//Points strictly increase.
//Stunned penguin implies 0 health.
//Always possible to reach a winning state.
