package core

import (
	"encoding/json"
	"io"
	"log"
	"net/http"
	"strings"
	"sync"
	"time"

	"github.com/KPMedical/go-kpmedical/common"
	"github.com/KPMedical/go-kpmedical/params"
	"github.com/robfig/cron/v3"
)

var (
	hospitalAddresses map[string]bool
	mutex             sync.RWMutex
	c                 *cron.Cron
)

// API Response
type APIResponse struct {
	Status  int64  `json:"status"`
	Success string `json:"success"`
	Message string `json:"message"`
	Data    struct {
		Amount    int64    `json:"amount"`
		Addresses []string `json:"addresses"`
	} `json:"data"`
}

// Call API for Updating global address map
func updateHospitalAddresses() {
	// Request API TODO: import request url
	resp, err := http.Get(params.HospitalCheckApiServer)
	if err != nil {
		log.Printf("Requesting API failed: %v", err)
		return
	}
	defer resp.Body.Close()

	// Read Body
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		log.Printf("Reading body failed: %v", err)
		return
	}

	// Parse JSON
	var apiResp APIResponse
	err = json.Unmarshal(body, &apiResp)
	if err != nil {
		log.Printf("Parsing JSON failed: %v", err)
		return
	}

	// Create new global map
	newAddresses := make(map[string]bool)
	for _, addr := range apiResp.Data.Addresses {
		lowerAddr := strings.ToLower(addr)
		newAddresses[lowerAddr] = true
	}

	// Update global map
	hospitalAddresses = newAddresses

	log.Printf("Hospital addresses updated. total %d addresses.", len(hospitalAddresses))
}

// Return if it's hospital's blockchain address
func isHospital(address string) bool {
	lowerAddress := strings.ToLower(address)
	return hospitalAddresses[lowerAddress]
}

// return true if from Address is registered as Hospital
func getIsHospital(from common.Address) bool {
	// Address to String
	fromStr := from.Hex()

	returnValue := isHospital(fromStr)

	return returnValue
}

// EveryKoreanTime 00:00 hospital address data update
func setupAndStartCron() {
	// Set Korean Time
	location, err := time.LoadLocation("Asia/Seoul")
	if err != nil {
		log.Fatalf("Failed to load location: %v", err)
	}

	// Create Cron Scheduler
	c := cron.New(cron.WithLocation(location))

	// Set Schedule time Every 00:00
	_, err = c.AddFunc("0 0 * * *", updateHospitalAddresses)
	if err != nil {
		log.Fatalf("Adding Cron Job failed: %v", err)
	}

	// CronJob Start
	c.Start()
	log.Println("CronJob Start.")
}

// Stop CronJob
func StopCron() {
	if c != nil {
		c.Stop()
		log.Println("CronJob Stopped")
	}
}

// Initialize global map var
func initHospitalAddresses() {
	mutex.Lock()
	hospitalAddresses = make(map[string]bool)
	mutex.Unlock()
}

// Import for cmd/main package
func InitializeHospitalSystem() {
	initHospitalAddresses()
	setupAndStartCron()
	updateHospitalAddresses()
}

// e066ae756363b5ba9a24917bf25f4c6d52577aaa
