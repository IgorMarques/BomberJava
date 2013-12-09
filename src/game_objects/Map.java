package game_objects;

import java.util.ArrayList;

import constants.Constants;
import core.Game;

import events.ExplodeEvent;
import events.MoveEvent;

import behavior.Explodable;
import behavior.MoveListener;

public class Map implements MoveListener {
	private /*@ spec_public @*/ int width = Constants.WIDTH;
	private /*@ spec_public @*/ int height = Constants.HEIGHT;
	
	private /*@ spec_public @*/ boolean[][] matrix;
	
	private /*@ spec_public @*/ Game game;
	
	/*@ requires game != null;
	 @ assignable this.game;
	 @ ensures this.game == game;
	 @ ensures \exists matrix instanceof boolean[height][width];
	 @ ensures \forall i = 0; i < width;
	 		   		\forall j = 0; i=j < height;
	 @					matrix[i][j] == true; 	
	 @*/
	public Map(Game game) {
		matrix = new boolean[height][width];
		this.game = game;
		game.setMap(this);
		
		for (int i = 0; i < width; i++)
			for (int j = 0; j < height; j++)
				matrix[j][i] = true; 
	}
	
	/*@ requires game != null;
	 @ also
	 @ requires (obj.getX() > width || obj.getY() > height || obj.getX() < 0 || obj.getY() < 0);
	 @ ensures \nothing;
	 @ also
	 @ requires (obj.getX() > width || obj.getY() > height || obj.getX() < 0 || obj.getY() < 0) == false;
	 @ assignable matrix[obj.getY()][obj.getX()]
	 @ ensures matrix[obj.getY()][obj.getX()] = obj.isTrepassable();
	 @*/
	public void addObject(GameObject obj) {
		if (obj.getX() > width || obj.getY() > height || obj.getX() < 0 || obj.getY() < 0) {
			return;
		}
		matrix[obj.getY()][obj.getX()] = obj.isTrepassable();
	}
	
	/*@ requires obj != null;
	@ assignable matrix();
	@ ensures (
	@ \forall int i; 0 <=i && i  < game.getObjects().length;
	@			game.getObjects()[i] != obj;
	@) 
	@ public constraint
	@	ensures \old(game.getObjects().length)-1 == game.getObjects.length;
	@ ensures matrix[obj.getY()][obj.getX()] == last.length == 0|| allTrespassable(last);
	@*/
	public void removeObject(GameObject obj) {
		GameObject[] last = objAt(obj.getX(), obj.getY());
		matrix[obj.getY()][obj.getX()] = last.length == 0|| allTrespassable(last);
	}
	
	/*@ requires \exists \forall int i; 1 <=i && i  < last.length;
	 *@						last[i].isTrepassable() == false;  
	 @ assignable \nothing;
	 @ ensures \result == false;
	 @ also
	 @ requires \exists \forall int i; 1 <=i && i  < last.length;
	 @						last[i].isTrepassable() == true;
	 @ assignable \nothing;
	 @ ensures \result == true; 
	 @*/
	private /*@ pure @*/ boolean allTrespassable(GameObject[] last) {
		for (GameObject obj: last) {
			if (!obj.isTrepassable())
				return false;
		}
		
		return true;
	}

	/*@ requires true;
	 @ assignable \nothing
	 @ ensures \result == \forall Object obj; obj.getX() == x && obj.getY() == y;
	 @*/
	public /*@ pure @*/ GameObject[] objAt(int x, int y) {
		ArrayList<GameObject> objects = new ArrayList<GameObject>();
		
		for (GameObject obj: game.getObjects()) {
			if (obj.getX() == x && obj.getY() == y)
				objects.add(obj);
		}
		
		return objects.toArray(new GameObject[objects.size()]);
	}
	
	/*@ requires true;
	 @ assignable \nothing;
	 @ ensures \result == this.width;
	 @*/
	public /*@ pure @*/ int getWidth(){
		return width;
	}
	
	/*@ requires true;
	 @ assignable \nothing;
	 @ ensures \result == this.height;
	 @*/
	public /*@ pure @*/  int getHeight(){
		return height;
	}
	
	/*@ public normal_behavior
		 @ requires x > 0;
		 @ requires y > 0;
		 @ requires x < this.width;
		 @ requires y < this.height;
		 @ assignable \nothing;
		 @ ensures \result == matrix[y][x];
	 @ also
	 @ public exceptional_behavior
	 @ requires x > 0 || x < this.width;
	 @ requires y > 0 || y < this.height;
	 @ singnals_only OutOfAreaException;
	@*/
	public /*@ pure @*/ boolean isMovableSpace(int x, int y) throws OutOfAreaException{
		return matrix[y][x];
	}
	
	/*@ requires x > 0;
	 @ requires y > 0;
	 @ requires x < this.width;
	 @ requires y < this.height;
	 @ assignable \nothing;
	 @ ensures \result == (-1 < y && y < getHeight() && -1 < x && x < getWidth() && isMovableSpace(x, y));
	@*/
	public /*@ pure @*/ boolean isValid(int x, int y) throws OutOfAreaException {
		return (-1 < y && y < getHeight() && -1 < x && x < getWidth() && isMovableSpace(x, y));
	}

	/*@ requires true;
	 @ requires e.getLastY() < this.height;
	 @ requires e.getLastX() < this.width;
	 @ assignable matrix;
	 @ ensures matrix[e.getLastY][e.getLastX] = objAt(lastX, lastY).length == 0 || allTrespassable(objAt(lastX, lastY));
	 @ ensures matrix[e.getObjMoved().getY()][e.getObjMoved().getX()] = e.getObjMoved().isTrepassable();
	@ */
	public void objectMoved(MoveEvent e) {
		int lastY = e.getLastY();
		int lastX = e.getLastX();
		GameObject objMoved = e.getObjMoved();
		GameObject[] last = objAt(lastX, lastY);
				
		matrix[lastY][lastX] = last.length == 0 || allTrespassable(last);
		matrix[objMoved.getY()][objMoved.getX()] = objMoved.isTrepassable();
	}

	/*@ requires x > 0;
	 @ requires y > 0;
	 @ requires x < this.width;
	 @ requires y < this.height;
	 @ assignable objAt(x, y);
	 @ ensures \forall i; 0 <=i && i  < objAt(x, y).lentgth;
	 @ 			requires objtAt(x,y) instanceof Explodable; 
	 @			ensures (Explodable) objAt(x, y)).exploded(new ExplodeEvent(bomb.getPlayerNumber())); 
	 @*/
	public void bomb(Bomb bomb, int x, int y) {
		GameObject[] affecteds = objAt(x, y);
		
		for (GameObject affected: affecteds) {
			if (affected instanceof Explodable) {
				((Explodable) affected).exploded(new ExplodeEvent(bomb.getPlayerNumber()));
			}
		}
	}
}
