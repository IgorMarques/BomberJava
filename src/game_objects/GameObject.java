package game_objects;

import core.Game;
import static constants.Constants.WIDTH;
import static constants.Constants.HEIGHT;

public abstract class GameObject {
	private /*@ spec_public @*/ int x;
	private /*@ spec_public @*/ int y;
	
	protected /*@ spec_public @*/ boolean trepassable = false;
	private /*@ spec_public @*/ boolean toRemove;
	
	private /*@ spec_public @*/ Game game;
	
	//@ public invariant x < WIDTH
	//@ public invariant y < HEIGHT
	
	/*@ requires x < WIDTH;
	@ requires y < HEIGHT;
	@ assignable x;
	@ assignable y;
	@ assignable game;
	@ ensures this.x == x;
	@ ensures this.y == y;
	@ ensures this.game == game@*/	
	public GameObject(Game game, int x, int y) {
		this.game = game;
		this.x = x;
		this.y = y;
		setToRemove(false);
	}
	
	
	/*@ requires true;
	@ assignable \nothing;
	@ ensures \result == "x:" + this.x "; y:"+ this.y @*/
	public /*@ pure @*/ String toString() {
		return "x: " + x + "; y: " + y;
	}
	
	/*@ requires true;
	@ assignable \nothing;
	@ ensures \result == this.game @*/
	public /*@ pure @*/ Game getGame() {
		return game;
	}

	/*@ requires true;
	@ assignable \nothing;
	@ ensures \result == this.x @*/
	public /*@ pure @*/ int getX() {
		return x;
	}
	
	/*@ requires x < WIDTH;
	 @ assignable x;
	 @ ensures this.x == x;@*/
	public void setX(int x) {
		this.x = x;
	}

	/*@ requires true;
	@ assignable \nothing;
	@ ensures \result == this.y @*/
	public /*@ pure @*/ int getY() {
		return y;
	}

	/*@ requires y < HEIGHT;
	 @ assignable y;
	 @ ensures this.y == y;@*/
	public void setY(int y) {
		this.y = y;
	}

	/*@ requires true;
	@ assignable \nothing;
	@ ensures \result == this.trepassable @*/
	public /*@ pure @*/ boolean isTrepassable() {		
		return trepassable;
	}
	
	public abstract void update(double delta);

	/*@ requires true;
	@ assignable \nothing;
	@ ensures \result == this.toRemove @*/
	public /*@ pure @*/ boolean isToRemove() {
		return toRemove;
	}
	
	/*@ requires true;
	 @ assignable toRemove;
	 @ ensures this.toRemove == toRemove;@*/
	public void setToRemove(boolean toRemove) {
		this.toRemove = toRemove;
	}
}
