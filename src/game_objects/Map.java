package game_objects;

import java.util.ArrayList;

import constants.Constants;
import core.Game;

import events.ExplodeEvent;
import events.MoveEvent;

import behavior.Explodable;
import behavior.MoveListener;

public class Map implements MoveListener {
	private int width = Constants.WIDTH;
	private int height = Constants.HEIGHT;
	
	private boolean[][] matrix;
	
	private Game game;
	
	public Map(Game game) {
		matrix = new boolean[height][width];
		this.game = game;
		game.setMap(this);
		
		for (int i = 0; i < width; i++)
			for (int j = 0; j < height; j++)
				matrix[j][i] = true; 
	}
	
	public void addObject(GameObject obj) {
		if (obj.getX() > width || obj.getY() > height || obj.getX() < 0 || obj.getY() < 0) {
			return;
		}
		matrix[obj.getY()][obj.getX()] = obj.isTrepassable();
	}
	
	public void removeObject(GameObject obj) {
		GameObject[] last = objAt(obj.getX(), obj.getY());
		matrix[obj.getY()][obj.getX()] = last.length == 0|| allTrespassable(last);
	}
	
	private boolean allTrespassable(GameObject[] last) {
		for (GameObject obj: last) {
			if (!obj.isTrepassable())
				return false;
		}
		
		return true;
	}

	public GameObject[] objAt(int x, int y) {
		ArrayList<GameObject> objects = new ArrayList<GameObject>();
		
		for (GameObject obj: game.getObjects()) {
			if (obj.getX() == x && obj.getY() == y)
				objects.add(obj);
		}
		
		return objects.toArray(new GameObject[objects.size()]);
	}
	
	public int getWidth(){
		return width;
	}
	
	public int getHeight(){
		return height;
	}
	
	public boolean isMovableSpace(int x, int y){
		return matrix[y][x];
	}
	
	public boolean isValid(int x, int y) {
		return (-1 < y && y < getHeight() && -1 < x && x < getWidth() && isMovableSpace(x, y));
	}

	public void objectMoved(MoveEvent e) {
		int lastY = e.getLastY();
		int lastX = e.getLastX();
		GameObject objMoved = e.getObjMoved();
		GameObject[] last = objAt(lastX, lastY);
				
		matrix[lastY][lastX] = last.length == 0 || allTrespassable(last);
		matrix[objMoved.getY()][objMoved.getX()] = objMoved.isTrepassable();
	}

	public void bomb(Bomb bomb, int x, int y) {
		GameObject[] affecteds = objAt(x, y);
		
		for (GameObject affected: affecteds) {
			if (affected instanceof Explodable) {
				((Explodable) affected).exploded(new ExplodeEvent(bomb.getPlayerNumber()));
			}
		}
	}
}
